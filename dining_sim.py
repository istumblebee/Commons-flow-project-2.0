"""
Dining Hall Flow Simulator v2.0
================================
Agent-based simulation for analyzing dining hall bottlenecks.

Controls:
    SPACE      - Pause/Resume simulation
    E          - Toggle Editor mode
    +/-        - Speed up/slow down simulation
    R          - Reset simulation
    Q/ESC      - Quit

Editor Mode:
    1          - Station tool (click+drag to draw)
    2          - Table tool (click to place)
    3          - Wall tool (click+drag to draw)
    4          - Entrance tool (click to place)
    5          - Exit tool (click to place)
    6          - Dish Return tool (click+drag)
    DELETE     - Delete item under cursor
    S          - Save layout
    L          - Load background image
    C          - Clear all
"""

import pygame
import json
import random
import math
import heapq
from pathlib import Path
from enum import Enum
from dataclasses import dataclass, field
from typing import Optional, List, Tuple
import tkinter as tk
from tkinter import filedialog

# ============================================================================
# CONFIGURATION
# ============================================================================

WINDOW_WIDTH = 1200
WINDOW_HEIGHT = 800
GRID_SIZE = 10  # For pathfinding

# Student settings
STUDENT_RADIUS = 6
STUDENT_SPAWN_RATE = 90  # frames between spawns
STUDENT_SPEED = 1.5
SEPARATION_RADIUS = 18  # How far apart students try to stay
SEPARATION_FORCE = 0.5

# Dietary distribution
DIET_DISTRIBUTION = {
    "omnivore": 0.60,
    "vegetarian": 0.25,
    "vegan": 0.15
}

# Timing (in frames at 60fps)
EAT_TIME_MIN = 600    # 10 seconds (scaled for demo, multiply by 60 for real minutes)
EAT_TIME_MAX = 1200   # 20 seconds
DISH_RETURN_TIME = 60
SERVICE_TIME_MULTIPLIER = 60  # Convert service_time seconds to frames

SECONDS_CHANCE = 0.20
DESSERT_CHANCE = 0.25

# Colors
COLORS = {
    "background": (30, 30, 35),
    "grid": (40, 40, 45),
    "wall": (80, 80, 90),
    "student_omnivore": (255, 220, 100),
    "student_vegetarian": (150, 255, 150),
    "student_vegan": (100, 255, 100),
    "student_has_food": (200, 150, 100),
    "table": (139, 90, 43),
    "table_occupied": (100, 60, 30),
    "dish_return": (120, 120, 140),
    "entrance": (100, 200, 100),
    "exit": (200, 100, 100),
    "queue_spot": (255, 255, 255),
    "text": (255, 255, 255),
    "text_dark": (20, 20, 20),
    "ui_bg": (20, 20, 25),
    "button": (60, 60, 70),
    "button_active": (80, 100, 120),
}


# ============================================================================
# ENUMS AND DATA CLASSES
# ============================================================================

class StudentState(Enum):
    ENTERING = "entering"
    WALKING_TO_STATION = "walking_to_station"
    QUEUING = "queuing"
    BEING_SERVED = "being_served"
    WALKING_TO_TABLE = "walking_to_table"
    EATING = "eating"
    WALKING_TO_DISH_RETURN = "walking_to_dish_return"
    QUEUING_DISH_RETURN = "queuing_dish_return"
    RETURNING_DISHES = "returning_dishes"
    WALKING_TO_EXIT = "walking_to_exit"
    EXITED = "exited"


class DietType(Enum):
    OMNIVORE = "omnivore"
    VEGETARIAN = "vegetarian"
    VEGAN = "vegan"


class EditorTool(Enum):
    STATION = 1
    TABLE = 2
    WALL = 3
    ENTRANCE = 4
    EXIT = 5
    DISH_RETURN = 6


@dataclass
class Station:
    name: str
    x: int
    y: int
    width: int
    height: int
    color: tuple
    food_type: str
    service_time: int
    capacity: int
    queue: list = field(default_factory=list)
    being_served: list = field(default_factory=list)
    service_timers: dict = field(default_factory=dict)
    queue_direction: str = "down"  # down, up, left, right

    @property
    def center(self):
        return (self.x + self.width // 2, self.y + self.height // 2)

    @property
    def service_positions(self) -> List[Tuple[int, int]]:
        """Positions where students stand while being served"""
        positions = []
        spacing = self.width // (self.capacity + 1)
        for i in range(self.capacity):
            px = self.x + spacing * (i + 1)
            py = self.y + self.height // 2
            positions.append((px, py))
        return positions

    def get_queue_positions(self, count: int) -> List[Tuple[int, int]]:
        """Get positions for students in queue"""
        positions = []
        spacing = SEPARATION_RADIUS + 4

        if self.queue_direction == "down":
            start_x = self.x + self.width // 2
            start_y = self.y + self.height + 15
            for i in range(count):
                positions.append((start_x, start_y + i * spacing))
        elif self.queue_direction == "up":
            start_x = self.x + self.width // 2
            start_y = self.y - 15
            for i in range(count):
                positions.append((start_x, start_y - i * spacing))
        elif self.queue_direction == "left":
            start_x = self.x - 15
            start_y = self.y + self.height // 2
            for i in range(count):
                positions.append((start_x - i * spacing, start_y))
        else:  # right
            start_x = self.x + self.width + 15
            start_y = self.y + self.height // 2
            for i in range(count):
                positions.append((start_x + i * spacing, start_y))

        return positions

    def can_eat_here(self, diet: DietType) -> bool:
        if self.food_type == "all" or self.food_type == "dessert":
            return True
        if diet == DietType.OMNIVORE:
            return True
        if diet == DietType.VEGETARIAN:
            return self.food_type in ["vegetarian", "vegan"]
        if diet == DietType.VEGAN:
            return self.food_type == "vegan"
        return False


@dataclass
class Table:
    x: int
    y: int
    seats: int
    occupied_by: list = field(default_factory=list)

    @property
    def center(self):
        return (self.x, self.y)

    @property
    def has_space(self):
        return len(self.occupied_by) < self.seats

    def get_seat_positions(self) -> List[Tuple[int, int]]:
        """Get positions around the table for students to sit"""
        positions = []
        radius = 25
        for i in range(self.seats):
            angle = (2 * math.pi * i) / self.seats
            px = self.x + int(radius * math.cos(angle))
            py = self.y + int(radius * math.sin(angle))
            positions.append((px, py))
        return positions


@dataclass
class Wall:
    x1: int
    y1: int
    x2: int
    y2: int
    thickness: int = 8

    def get_rect(self) -> pygame.Rect:
        x = min(self.x1, self.x2)
        y = min(self.y1, self.y2)
        w = max(abs(self.x2 - self.x1), self.thickness)
        h = max(abs(self.y2 - self.y1), self.thickness)
        return pygame.Rect(x, y, w, h)


@dataclass
class DishReturn:
    x: int
    y: int
    width: int
    height: int
    queue: list = field(default_factory=list)
    being_served: list = field(default_factory=list)
    capacity: int = 2

    @property
    def center(self):
        return (self.x + self.width // 2, self.y + self.height // 2)

    def get_queue_positions(self, count: int) -> List[Tuple[int, int]]:
        positions = []
        spacing = SEPARATION_RADIUS + 4
        start_x = self.x + self.width // 2
        start_y = self.y + self.height + 15
        for i in range(count):
            positions.append((start_x, start_y + i * spacing))
        return positions


@dataclass
class Entrance:
    x: int
    y: int
    spawn_rate: int = STUDENT_SPAWN_RATE

    @property
    def center(self):
        return (self.x, self.y)


@dataclass
class Exit:
    x: int
    y: int

    @property
    def center(self):
        return (self.x, self.y)


@dataclass
class Student:
    id: int
    x: float
    y: float
    diet: DietType
    state: StudentState = StudentState.ENTERING
    target: tuple = None
    path: list = field(default_factory=list)
    target_station: Station = None
    target_table: Table = None
    seat_position: tuple = None
    speed: float = STUDENT_SPEED
    eat_timer: int = 0
    has_food: bool = False
    meals_eaten: int = 0
    time_in_system: int = 0
    wait_time: int = 0
    vx: float = 0  # velocity for smooth movement
    vy: float = 0

    @property
    def color(self):
        if self.diet == DietType.VEGAN:
            return COLORS["student_vegan"]
        elif self.diet == DietType.VEGETARIAN:
            return COLORS["student_vegetarian"]
        return COLORS["student_omnivore"]

    @property
    def pos(self):
        return (self.x, self.y)


# ============================================================================
# PATHFINDING
# ============================================================================

class Pathfinder:
    """Simple A* pathfinding that avoids walls"""

    def __init__(self, width, height, grid_size):
        self.width = width
        self.height = height
        self.grid_size = grid_size
        self.cols = width // grid_size
        self.rows = height // grid_size
        self.obstacles = set()  # Grid cells that are blocked

    def update_obstacles(self, walls: List[Wall], stations: List[Station]):
        """Mark grid cells that contain walls or stations as obstacles"""
        self.obstacles.clear()

        for wall in walls:
            rect = wall.get_rect()
            for gx in range(rect.left // self.grid_size, (rect.right // self.grid_size) + 1):
                for gy in range(rect.top // self.grid_size, (rect.bottom // self.grid_size) + 1):
                    if 0 <= gx < self.cols and 0 <= gy < self.rows:
                        self.obstacles.add((gx, gy))

        # Stations are semi-obstacles (can queue near them but not walk through)
        for station in stations:
            for gx in range(station.x // self.grid_size, (station.x + station.width) // self.grid_size + 1):
                for gy in range(station.y // self.grid_size, (station.y + station.height) // self.grid_size + 1):
                    if 0 <= gx < self.cols and 0 <= gy < self.rows:
                        self.obstacles.add((gx, gy))

    def heuristic(self, a, b):
        return abs(a[0] - b[0]) + abs(a[1] - b[1])

    def get_neighbors(self, pos):
        """Get walkable neighboring cells"""
        x, y = pos
        neighbors = []
        for dx, dy in [(0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)]:
            nx, ny = x + dx, y + dy
            if 0 <= nx < self.cols and 0 <= ny < self.rows:
                if (nx, ny) not in self.obstacles:
                    neighbors.append((nx, ny))
        return neighbors

    def find_path(self, start: Tuple[int, int], goal: Tuple[int, int]) -> List[Tuple[int, int]]:
        """Find path from start to goal, returns list of world coordinates"""
        # Convert to grid coordinates
        start_grid = (int(start[0] // self.grid_size), int(start[1] // self.grid_size))
        goal_grid = (int(goal[0] // self.grid_size), int(goal[1] // self.grid_size))

        # Clamp to valid range
        start_grid = (max(0, min(start_grid[0], self.cols-1)), max(0, min(start_grid[1], self.rows-1)))
        goal_grid = (max(0, min(goal_grid[0], self.cols-1)), max(0, min(goal_grid[1], self.rows-1)))

        # If start or goal is in obstacle, find nearest free cell
        if start_grid in self.obstacles:
            start_grid = self._find_nearest_free(start_grid)
        if goal_grid in self.obstacles:
            goal_grid = self._find_nearest_free(goal_grid)

        if start_grid is None or goal_grid is None:
            return [goal]  # Fallback: direct path

        # A* search
        frontier = [(0, start_grid)]
        came_from = {start_grid: None}
        cost_so_far = {start_grid: 0}

        while frontier:
            _, current = heapq.heappop(frontier)

            if current == goal_grid:
                break

            for next_pos in self.get_neighbors(current):
                # Diagonal movement costs more
                move_cost = 1.4 if abs(next_pos[0] - current[0]) + abs(next_pos[1] - current[1]) == 2 else 1
                new_cost = cost_so_far[current] + move_cost

                if next_pos not in cost_so_far or new_cost < cost_so_far[next_pos]:
                    cost_so_far[next_pos] = new_cost
                    priority = new_cost + self.heuristic(next_pos, goal_grid)
                    heapq.heappush(frontier, (priority, next_pos))
                    came_from[next_pos] = current

        # Reconstruct path
        if goal_grid not in came_from:
            return [goal]  # No path found, try direct

        path = []
        current = goal_grid
        while current is not None:
            # Convert back to world coordinates (center of grid cell)
            wx = current[0] * self.grid_size + self.grid_size // 2
            wy = current[1] * self.grid_size + self.grid_size // 2
            path.append((wx, wy))
            current = came_from[current]

        path.reverse()

        # Simplify path - remove intermediate points on straight lines
        if len(path) > 2:
            simplified = [path[0]]
            for i in range(1, len(path) - 1):
                prev = simplified[-1]
                curr = path[i]
                next_p = path[i + 1]
                # Keep point if direction changes
                dx1 = curr[0] - prev[0]
                dy1 = curr[1] - prev[1]
                dx2 = next_p[0] - curr[0]
                dy2 = next_p[1] - curr[1]
                if (dx1, dy1) != (dx2, dy2):
                    simplified.append(curr)
            simplified.append(path[-1])
            path = simplified

        # Add the actual goal position at the end
        path.append(goal)

        return path[1:] if len(path) > 1 else [goal]  # Skip start position

    def _find_nearest_free(self, pos):
        """Find nearest non-obstacle cell"""
        for radius in range(1, 20):
            for dx in range(-radius, radius + 1):
                for dy in range(-radius, radius + 1):
                    check = (pos[0] + dx, pos[1] + dy)
                    if 0 <= check[0] < self.cols and 0 <= check[1] < self.rows:
                        if check not in self.obstacles:
                            return check
        return None


# ============================================================================
# MAIN SIMULATION
# ============================================================================

class DiningHallSimulation:
    def __init__(self):
        pygame.init()
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        pygame.display.set_caption("Dining Hall Flow Simulator v2.0")
        self.clock = pygame.time.Clock()
        self.font = pygame.font.Font(None, 24)
        self.small_font = pygame.font.Font(None, 18)
        self.large_font = pygame.font.Font(None, 32)

        # Simulation state
        self.running = True
        self.paused = True  # Start paused so user can set up
        self.speed = 1.0
        self.frame_count = 0
        self.student_id_counter = 0

        # Editor state
        self.editor_mode = True  # Start in editor mode
        self.current_tool = EditorTool.STATION
        self.drawing = False
        self.draw_start = None
        self.selected_item = None

        # Layout elements
        self.stations: List[Station] = []
        self.tables: List[Table] = []
        self.walls: List[Wall] = []
        self.entrances: List[Entrance] = []
        self.exits: List[Exit] = []
        self.dish_returns: List[DishReturn] = []

        # Students
        self.students: List[Student] = []

        # Pathfinding
        self.pathfinder = Pathfinder(WINDOW_WIDTH, WINDOW_HEIGHT, GRID_SIZE)

        # Background image
        self.background_image = None
        self.background_path = None

        # Stats
        self.total_students_served = 0
        self.total_wait_time = 0
        self.total_time_in_system = 0

        # Load existing layout if available
        self.load_layout()

        # Station config popup state
        self.configuring_station = None
        self.config_input = ""
        self.config_field = 0  # 0=name, 1=food_type, 2=service_time, 3=capacity

    def load_background_image(self, path: str = None):
        """Load a background image"""
        if path is None:
            # Open file dialog
            root = tk.Tk()
            root.withdraw()
            path = filedialog.askopenfilename(
                title="Select Dining Hall Image",
                filetypes=[("Image files", "*.png *.jpg *.jpeg *.bmp *.gif")]
            )
            root.destroy()

        if path:
            try:
                self.background_image = pygame.image.load(path)
                self.background_image = pygame.transform.scale(
                    self.background_image,
                    (WINDOW_WIDTH, WINDOW_HEIGHT)
                )
                self.background_path = path
                print(f"Loaded background: {path}")
            except Exception as e:
                print(f"Error loading image: {e}")

    def load_layout(self):
        """Load layout from config file"""
        config_path = Path("config/layout.json")
        if not config_path.exists():
            config_path = Path("config/stations.json")  # Try old format

        if config_path.exists():
            try:
                with open(config_path) as f:
                    data = json.load(f)

                # Load background
                if data.get("background_image"):
                    self.load_background_image(data["background_image"])

                # Load stations
                for s in data.get("stations", []):
                    station = Station(
                        name=s["name"],
                        x=s["x"], y=s["y"],
                        width=s["width"], height=s["height"],
                        color=tuple(s["color"]),
                        food_type=s.get("food_type", "all"),
                        service_time=s.get("service_time", 6),
                        capacity=s.get("capacity", 3),
                        queue_direction=s.get("queue_direction", "down")
                    )
                    self.stations.append(station)

                # Load tables
                for t in data.get("tables", []):
                    self.tables.append(Table(x=t["x"], y=t["y"], seats=t.get("seats", 4)))

                # Load walls
                for w in data.get("walls", []):
                    self.walls.append(Wall(x1=w["x1"], y1=w["y1"], x2=w["x2"], y2=w["y2"]))

                # Load entrances
                for e in data.get("entrances", []):
                    self.entrances.append(Entrance(x=e["x"], y=e["y"]))

                # Load exits
                for e in data.get("exits", []):
                    self.exits.append(Exit(x=e["x"], y=e["y"]))

                # Load dish returns
                for d in data.get("dish_returns", []):
                    self.dish_returns.append(DishReturn(
                        x=d["x"], y=d["y"],
                        width=d.get("width", 60), height=d.get("height", 40)
                    ))

                # Legacy: single dish_return
                if "dish_return" in data and not self.dish_returns:
                    d = data["dish_return"]
                    if d:
                        self.dish_returns.append(DishReturn(
                            x=d["x"], y=d["y"],
                            width=d.get("width", 60), height=d.get("height", 40)
                        ))

                # Legacy: single entrance/exit
                if "entrance" in data and not self.entrances:
                    e = data["entrance"]
                    self.entrances.append(Entrance(x=e["x"], y=e["y"]))
                if "exit" in data and not self.exits:
                    e = data["exit"]
                    self.exits.append(Exit(x=e["x"], y=e["y"]))

                self.update_pathfinding()
                print(f"Loaded layout: {len(self.stations)} stations, {len(self.tables)} tables, {len(self.walls)} walls")

            except Exception as e:
                print(f"Error loading layout: {e}")
                import traceback
                traceback.print_exc()

    def save_layout(self):
        """Save layout to config file"""
        data = {
            "background_image": self.background_path,
            "stations": [
                {
                    "name": s.name, "x": s.x, "y": s.y,
                    "width": s.width, "height": s.height,
                    "color": list(s.color), "food_type": s.food_type,
                    "service_time": s.service_time, "capacity": s.capacity,
                    "queue_direction": s.queue_direction
                }
                for s in self.stations
            ],
            "tables": [{"x": t.x, "y": t.y, "seats": t.seats} for t in self.tables],
            "walls": [{"x1": w.x1, "y1": w.y1, "x2": w.x2, "y2": w.y2} for w in self.walls],
            "entrances": [{"x": e.x, "y": e.y} for e in self.entrances],
            "exits": [{"x": e.x, "y": e.y} for e in self.exits],
            "dish_returns": [
                {"x": d.x, "y": d.y, "width": d.width, "height": d.height}
                for d in self.dish_returns
            ]
        }

        Path("config").mkdir(exist_ok=True)
        with open("config/layout.json", "w") as f:
            json.dump(data, f, indent=2)
        print("Layout saved to config/layout.json")

    def update_pathfinding(self):
        """Update pathfinding grid with current obstacles"""
        self.pathfinder.update_obstacles(self.walls, self.stations)

    def spawn_student(self, entrance: Entrance):
        """Create a new student at an entrance"""
        # Determine diet
        r = random.random()
        cumulative = 0
        diet = DietType.OMNIVORE
        for diet_name, prob in DIET_DISTRIBUTION.items():
            cumulative += prob
            if r <= cumulative:
                diet = DietType[diet_name.upper()]
                break

        student = Student(
            id=self.student_id_counter,
            x=entrance.x + random.randint(-10, 10),
            y=entrance.y + random.randint(-10, 10),
            diet=diet,
            speed=random.uniform(STUDENT_SPEED * 0.8, STUDENT_SPEED * 1.2)
        )
        self.student_id_counter += 1
        self.students.append(student)

    def get_compatible_stations(self, student: Student, include_dessert=False) -> List[Station]:
        """Get stations where student can eat"""
        stations = []
        for s in self.stations:
            if s.food_type == "dessert" and not include_dessert:
                continue
            if s.can_eat_here(student.diet):
                stations.append(s)
        return stations

    def get_dessert_stations(self) -> List[Station]:
        """Get dessert stations"""
        return [s for s in self.stations if s.food_type == "dessert"]

    def find_available_table(self) -> Optional[Table]:
        """Find a table with space"""
        available = [t for t in self.tables if t.has_space]
        if available:
            # Prefer tables with some people (more realistic)
            occupied = [t for t in available if len(t.occupied_by) > 0]
            if occupied and random.random() < 0.6:
                return random.choice(occupied)
            return random.choice(available)
        return None

    def find_nearest_dish_return(self, pos: Tuple[float, float]) -> Optional[DishReturn]:
        """Find nearest dish return"""
        if not self.dish_returns:
            return None
        nearest = min(self.dish_returns, key=lambda d:
            math.sqrt((d.center[0] - pos[0])**2 + (d.center[1] - pos[1])**2))
        return nearest

    def find_nearest_exit(self, pos: Tuple[float, float]) -> Optional[Exit]:
        """Find nearest exit"""
        if not self.exits:
            return None
        nearest = min(self.exits, key=lambda e:
            math.sqrt((e.x - pos[0])**2 + (e.y - pos[1])**2))
        return nearest

    def choose_station(self, student: Student) -> Optional[Station]:
        """AI: Choose a station based on queue length and preferences"""
        compatible = self.get_compatible_stations(student)
        if not compatible:
            return None

        # Score stations: prefer shorter queues
        scored = []
        for station in compatible:
            queue_len = len(station.queue) + len(station.being_served)
            # Base score inversely proportional to queue
            score = 100 - queue_len * 15
            # Add randomness for variety
            score += random.randint(-10, 10)
            scored.append((score, station))

        scored.sort(reverse=True, key=lambda x: x[0])
        return scored[0][1]

    def apply_separation(self, student: Student):
        """Push students apart so they don't overlap"""
        sep_x, sep_y = 0, 0
        neighbor_count = 0

        for other in self.students:
            if other.id == student.id or other.state == StudentState.EXITED:
                continue
            if other.state == StudentState.EATING:  # Don't push eating students
                continue

            dx = student.x - other.x
            dy = student.y - other.y
            dist = math.sqrt(dx*dx + dy*dy)

            if dist < SEPARATION_RADIUS and dist > 0:
                # Push away from other student
                force = (SEPARATION_RADIUS - dist) / SEPARATION_RADIUS
                sep_x += (dx / dist) * force
                sep_y += (dy / dist) * force
                neighbor_count += 1

        if neighbor_count > 0:
            student.vx += sep_x * SEPARATION_FORCE
            student.vy += sep_y * SEPARATION_FORCE

    def check_wall_collision(self, x: float, y: float, radius: float = STUDENT_RADIUS) -> bool:
        """Check if position collides with any wall"""
        for wall in self.walls:
            rect = wall.get_rect()
            # Expand rect by radius
            expanded = rect.inflate(radius * 2, radius * 2)
            if expanded.collidepoint(x, y):
                return True
        return False

    def move_student_toward(self, student: Student, target: Tuple[float, float]) -> bool:
        """Move student toward target with collision avoidance, return True if arrived"""
        if student.path:
            # Follow path
            next_point = student.path[0]
            dx = next_point[0] - student.x
            dy = next_point[1] - student.y
            dist = math.sqrt(dx*dx + dy*dy)

            if dist < student.speed * self.speed * 2:
                # Reached waypoint
                student.path.pop(0)
                if not student.path:
                    # Reached final target
                    student.x, student.y = target
                    return True
            else:
                # Move toward waypoint
                student.vx = (dx / dist) * student.speed
                student.vy = (dy / dist) * student.speed
        else:
            # Direct movement
            dx = target[0] - student.x
            dy = target[1] - student.y
            dist = math.sqrt(dx*dx + dy*dy)

            if dist < student.speed * self.speed * 2:
                student.x, student.y = target
                return True

            student.vx = (dx / dist) * student.speed
            student.vy = (dy / dist) * student.speed

        # Apply separation from other students
        self.apply_separation(student)

        # Apply velocity with wall collision check
        new_x = student.x + student.vx * self.speed
        new_y = student.y + student.vy * self.speed

        # Simple wall avoidance
        if not self.check_wall_collision(new_x, new_y):
            student.x = new_x
            student.y = new_y
        else:
            # Try sliding along wall
            if not self.check_wall_collision(new_x, student.y):
                student.x = new_x
            elif not self.check_wall_collision(student.x, new_y):
                student.y = new_y

        # Clamp to screen
        student.x = max(STUDENT_RADIUS, min(WINDOW_WIDTH - STUDENT_RADIUS, student.x))
        student.y = max(STUDENT_RADIUS, min(WINDOW_HEIGHT - STUDENT_RADIUS, student.y))

        return False

    def update_student(self, student: Student):
        """Update student state machine"""
        student.time_in_system += 1

        if student.state == StudentState.ENTERING:
            # Just spawned - pick a station
            station = self.choose_station(student)
            if station:
                student.target_station = station
                queue_pos = station.get_queue_positions(len(station.queue) + 1)[-1]
                student.target = queue_pos
                student.path = self.pathfinder.find_path(student.pos, queue_pos)
                student.state = StudentState.WALKING_TO_STATION
            elif self.exits:
                # No compatible stations, leave
                exit_point = self.find_nearest_exit(student.pos)
                student.target = exit_point.center
                student.path = self.pathfinder.find_path(student.pos, student.target)
                student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_STATION:
            if self.move_student_toward(student, student.target):
                # Arrived at queue position
                student.target_station.queue.append(student)
                student.state = StudentState.QUEUING

        elif student.state == StudentState.QUEUING:
            student.wait_time += 1
            station = student.target_station

            # Update queue position
            if student in station.queue:
                idx = station.queue.index(student)
                positions = station.get_queue_positions(len(station.queue))
                if idx < len(positions):
                    target_pos = positions[idx]
                    self.move_student_toward(student, target_pos)

            # Check if can be served
            if student in station.queue[:station.capacity]:
                if len(station.being_served) < station.capacity:
                    station.queue.remove(student)
                    station.being_served.append(student)
                    station.service_timers[student.id] = station.service_time * SERVICE_TIME_MULTIPLIER
                    student.state = StudentState.BEING_SERVED

        elif student.state == StudentState.BEING_SERVED:
            station = student.target_station

            # Move to service position
            service_positions = station.service_positions
            if station.being_served:
                idx = station.being_served.index(student) if student in station.being_served else 0
                if idx < len(service_positions):
                    self.move_student_toward(student, service_positions[idx])

            # Count down service time
            if student.id in station.service_timers:
                station.service_timers[student.id] -= self.speed

                if station.service_timers[student.id] <= 0:
                    # Done being served
                    if student in station.being_served:
                        station.being_served.remove(student)
                    del station.service_timers[student.id]
                    student.has_food = True
                    student.meals_eaten += 1

                    # Find a table
                    table = self.find_available_table()
                    if table:
                        student.target_table = table
                        table.occupied_by.append(student)
                        seats = table.get_seat_positions()
                        seat_idx = len(table.occupied_by) - 1
                        student.seat_position = seats[seat_idx % len(seats)]
                        student.target = student.seat_position
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_TABLE
                    else:
                        # No tables, go to dish return
                        dish_return = self.find_nearest_dish_return(student.pos)
                        if dish_return:
                            student.target = dish_return.center
                            student.path = self.pathfinder.find_path(student.pos, student.target)
                            student.state = StudentState.WALKING_TO_DISH_RETURN

        elif student.state == StudentState.WALKING_TO_TABLE:
            if self.move_student_toward(student, student.target):
                student.eat_timer = random.randint(EAT_TIME_MIN, EAT_TIME_MAX)
                student.state = StudentState.EATING

        elif student.state == StudentState.EATING:
            student.eat_timer -= self.speed
            # Stay at seat position
            if student.seat_position:
                self.move_student_toward(student, student.seat_position)

            if student.eat_timer <= 0:
                student.has_food = False
                if student.target_table and student in student.target_table.occupied_by:
                    student.target_table.occupied_by.remove(student)

                # Decide next action
                if student.meals_eaten == 1:
                    if random.random() < DESSERT_CHANCE:
                        desserts = self.get_dessert_stations()
                        if desserts:
                            student.target_station = random.choice(desserts)
                            queue_pos = student.target_station.get_queue_positions(
                                len(student.target_station.queue) + 1)[-1]
                            student.target = queue_pos
                            student.path = self.pathfinder.find_path(student.pos, student.target)
                            student.state = StudentState.WALKING_TO_STATION
                            return
                    elif random.random() < SECONDS_CHANCE:
                        station = self.choose_station(student)
                        if station:
                            student.target_station = station
                            queue_pos = station.get_queue_positions(len(station.queue) + 1)[-1]
                            student.target = queue_pos
                            student.path = self.pathfinder.find_path(student.pos, student.target)
                            student.state = StudentState.WALKING_TO_STATION
                            return

                # Go to dish return
                dish_return = self.find_nearest_dish_return(student.pos)
                if dish_return:
                    queue_pos = dish_return.get_queue_positions(len(dish_return.queue) + 1)[-1]
                    student.target = queue_pos
                    student.path = self.pathfinder.find_path(student.pos, student.target)
                    student.state = StudentState.WALKING_TO_DISH_RETURN
                else:
                    # No dish return, go to exit
                    exit_point = self.find_nearest_exit(student.pos)
                    if exit_point:
                        student.target = exit_point.center
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_DISH_RETURN:
            if self.move_student_toward(student, student.target):
                # Find which dish return we're at
                for dr in self.dish_returns:
                    dist = math.sqrt((dr.center[0] - student.x)**2 + (dr.center[1] - student.y)**2)
                    if dist < 50:
                        dr.queue.append(student)
                        student.state = StudentState.QUEUING_DISH_RETURN
                        break
                else:
                    # Couldn't find dish return, go to exit
                    exit_point = self.find_nearest_exit(student.pos)
                    if exit_point:
                        student.target = exit_point.center
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.QUEUING_DISH_RETURN:
            student.wait_time += 1
            # Find our dish return
            for dr in self.dish_returns:
                if student in dr.queue:
                    idx = dr.queue.index(student)
                    positions = dr.get_queue_positions(len(dr.queue))
                    if idx < len(positions):
                        self.move_student_toward(student, positions[idx])

                    # Check if can return dishes
                    if idx < dr.capacity and len(dr.being_served) < dr.capacity:
                        dr.queue.remove(student)
                        dr.being_served.append(student)
                        student.eat_timer = DISH_RETURN_TIME
                        student.state = StudentState.RETURNING_DISHES
                    break

        elif student.state == StudentState.RETURNING_DISHES:
            student.eat_timer -= self.speed

            # Move to dish return center
            for dr in self.dish_returns:
                if student in dr.being_served:
                    self.move_student_toward(student, dr.center)
                    break

            if student.eat_timer <= 0:
                # Done returning dishes
                for dr in self.dish_returns:
                    if student in dr.being_served:
                        dr.being_served.remove(student)
                        break

                exit_point = self.find_nearest_exit(student.pos)
                if exit_point:
                    student.target = exit_point.center
                    student.path = self.pathfinder.find_path(student.pos, student.target)
                    student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_EXIT:
            if self.move_student_toward(student, student.target):
                student.state = StudentState.EXITED
                self.total_students_served += 1
                self.total_wait_time += student.wait_time
                self.total_time_in_system += student.time_in_system

    def update(self):
        """Main update loop"""
        if self.paused or self.editor_mode:
            return

        self.frame_count += 1

        # Spawn students from entrances
        for entrance in self.entrances:
            spawn_rate = max(1, int(entrance.spawn_rate / self.speed))
            if self.frame_count % spawn_rate == 0:
                self.spawn_student(entrance)

        # Update all students
        for student in self.students:
            if student.state != StudentState.EXITED:
                self.update_student(student)

        # Cleanup exited students (keep recent for stats)
        exited = [s for s in self.students if s.state == StudentState.EXITED]
        if len(exited) > 50:
            for s in exited[:-50]:
                self.students.remove(s)

    def draw(self):
        """Render everything"""
        # Background
        if self.background_image:
            self.screen.blit(self.background_image, (0, 0))
        else:
            self.screen.fill(COLORS["background"])
            # Draw grid in editor mode
            if self.editor_mode:
                for x in range(0, WINDOW_WIDTH, 50):
                    pygame.draw.line(self.screen, COLORS["grid"], (x, 0), (x, WINDOW_HEIGHT))
                for y in range(0, WINDOW_HEIGHT, 50):
                    pygame.draw.line(self.screen, COLORS["grid"], (0, y), (WINDOW_WIDTH, y))

        # Draw walls
        for wall in self.walls:
            pygame.draw.rect(self.screen, COLORS["wall"], wall.get_rect())

        # Draw entrances
        for entrance in self.entrances:
            pygame.draw.circle(self.screen, COLORS["entrance"], entrance.center, 20)
            pygame.draw.circle(self.screen, (255, 255, 255), entrance.center, 20, 2)
            text = self.small_font.render("IN", True, COLORS["text_dark"])
            self.screen.blit(text, (entrance.x - 8, entrance.y - 6))

        # Draw exits
        for exit_point in self.exits:
            pygame.draw.circle(self.screen, COLORS["exit"], exit_point.center, 20)
            pygame.draw.circle(self.screen, (255, 255, 255), exit_point.center, 20, 2)
            text = self.small_font.render("OUT", True, COLORS["text_dark"])
            self.screen.blit(text, (exit_point.x - 12, exit_point.y - 6))

        # Draw dish returns
        for dr in self.dish_returns:
            pygame.draw.rect(self.screen, COLORS["dish_return"],
                           pygame.Rect(dr.x, dr.y, dr.width, dr.height))
            pygame.draw.rect(self.screen, (255, 255, 255),
                           pygame.Rect(dr.x, dr.y, dr.width, dr.height), 2)
            text = self.small_font.render("DISHES", True, COLORS["text_dark"])
            self.screen.blit(text, (dr.x + 5, dr.y + dr.height//2 - 6))
            # Queue count
            if dr.queue:
                q_text = self.small_font.render(f"Q:{len(dr.queue)}", True, COLORS["text"])
                self.screen.blit(q_text, (dr.x, dr.y + dr.height + 5))

        # Draw tables
        for table in self.tables:
            color = COLORS["table_occupied"] if table.occupied_by else COLORS["table"]
            pygame.draw.circle(self.screen, color, table.center, 22)
            pygame.draw.circle(self.screen, (200, 200, 200), table.center, 22, 2)
            # Seat count
            text = self.small_font.render(f"{len(table.occupied_by)}/{table.seats}", True, COLORS["text"])
            self.screen.blit(text, (table.x - 12, table.y - 6))

        # Draw stations
        for station in self.stations:
            # Station body
            pygame.draw.rect(self.screen, station.color,
                           pygame.Rect(station.x, station.y, station.width, station.height))
            pygame.draw.rect(self.screen, (255, 255, 255),
                           pygame.Rect(station.x, station.y, station.width, station.height), 2)

            # Station name
            text = self.small_font.render(station.name, True, COLORS["text_dark"])
            self.screen.blit(text, (station.x + 4, station.y + 4))

            # Queue indicator
            queue_len = len(station.queue)
            if queue_len > 0:
                q_color = (255, 100, 100) if queue_len > 5 else COLORS["text"]
                q_text = self.small_font.render(f"Queue: {queue_len}", True, q_color)
                self.screen.blit(q_text, (station.x, station.y + station.height + 5))

        # Draw students
        for student in self.students:
            if student.state == StudentState.EXITED:
                continue

            # Student body
            pygame.draw.circle(self.screen, student.color,
                             (int(student.x), int(student.y)), STUDENT_RADIUS)

            # Food indicator
            if student.has_food:
                pygame.draw.circle(self.screen, COLORS["student_has_food"],
                                 (int(student.x), int(student.y)), 3)

            # Outline for queuing students
            if student.state in [StudentState.QUEUING, StudentState.QUEUING_DISH_RETURN]:
                pygame.draw.circle(self.screen, (255, 255, 255),
                                 (int(student.x), int(student.y)), STUDENT_RADIUS, 1)

        # Draw UI
        self.draw_ui()

        pygame.display.flip()

    def draw_ui(self):
        """Draw UI overlay"""
        # Stats panel (top left)
        active = len([s for s in self.students if s.state != StudentState.EXITED])

        avg_wait = 0
        avg_time = 0
        if self.total_students_served > 0:
            avg_wait = (self.total_wait_time / self.total_students_served) / 60
            avg_time = (self.total_time_in_system / self.total_students_served) / 60

        # Draw panel background
        panel_rect = pygame.Rect(5, 5, 220, 160)
        pygame.draw.rect(self.screen, COLORS["ui_bg"], panel_rect)
        pygame.draw.rect(self.screen, (100, 100, 100), panel_rect, 1)

        stats = [
            f"Active: {active}  |  Served: {self.total_students_served}",
            f"Avg Wait: {avg_wait:.1f}s",
            f"Avg Total: {avg_time:.1f}s",
            f"Speed: {self.speed:.1f}x",
            "",
            "SPACE=Run  E=Editor  R=Reset",
            "+/- Speed  S=Save  Q=Quit"
        ]

        if self.paused and not self.editor_mode:
            stats.insert(0, "[ PAUSED ]")
        elif self.editor_mode:
            stats.insert(0, "[ EDITOR MODE ]")

        y = 12
        for stat in stats:
            text = self.small_font.render(stat, True, COLORS["text"])
            self.screen.blit(text, (12, y))
            y += 18

        # Bottleneck warnings
        y_warn = 180
        for station in self.stations:
            if len(station.queue) > 5:
                warn_text = f"! {station.name}: {len(station.queue)} waiting"
                text = self.font.render(warn_text, True, (255, 100, 100))
                pygame.draw.rect(self.screen, (50, 0, 0), (5, y_warn, text.get_width() + 10, 25))
                self.screen.blit(text, (10, y_warn + 3))
                y_warn += 28

        # Editor toolbar
        if self.editor_mode:
            self.draw_editor_toolbar()

    def draw_editor_toolbar(self):
        """Draw editor toolbar"""
        toolbar_y = WINDOW_HEIGHT - 60
        pygame.draw.rect(self.screen, COLORS["ui_bg"],
                        (0, toolbar_y, WINDOW_WIDTH, 60))
        pygame.draw.line(self.screen, (100, 100, 100),
                        (0, toolbar_y), (WINDOW_WIDTH, toolbar_y))

        tools = [
            (EditorTool.STATION, "1:Station"),
            (EditorTool.TABLE, "2:Table"),
            (EditorTool.WALL, "3:Wall"),
            (EditorTool.ENTRANCE, "4:Entrance"),
            (EditorTool.EXIT, "5:Exit"),
            (EditorTool.DISH_RETURN, "6:Dishes"),
        ]

        x = 20
        for tool, label in tools:
            is_active = self.current_tool == tool
            color = COLORS["button_active"] if is_active else COLORS["button"]
            btn_rect = pygame.Rect(x, toolbar_y + 10, 90, 40)
            pygame.draw.rect(self.screen, color, btn_rect)
            pygame.draw.rect(self.screen, (150, 150, 150) if is_active else (100, 100, 100), btn_rect, 2)

            text = self.small_font.render(label, True, COLORS["text"])
            self.screen.blit(text, (x + 10, toolbar_y + 22))
            x += 100

        # Additional controls
        controls = "DEL=Delete  S=Save  L=Load Image  C=Clear  SPACE=Run Simulation"
        text = self.small_font.render(controls, True, (180, 180, 180))
        self.screen.blit(text, (x + 30, toolbar_y + 22))

    def get_item_at(self, pos) -> tuple:
        """Get item at position, returns (type, item) or (None, None)"""
        x, y = pos

        # Check stations
        for station in self.stations:
            if station.x <= x <= station.x + station.width:
                if station.y <= y <= station.y + station.height:
                    return ("station", station)

        # Check tables
        for table in self.tables:
            dist = math.sqrt((table.x - x)**2 + (table.y - y)**2)
            if dist < 25:
                return ("table", table)

        # Check walls
        for wall in self.walls:
            if wall.get_rect().collidepoint(x, y):
                return ("wall", wall)

        # Check entrances
        for entrance in self.entrances:
            dist = math.sqrt((entrance.x - x)**2 + (entrance.y - y)**2)
            if dist < 25:
                return ("entrance", entrance)

        # Check exits
        for exit_point in self.exits:
            dist = math.sqrt((exit_point.x - x)**2 + (exit_point.y - y)**2)
            if dist < 25:
                return ("exit", exit_point)

        # Check dish returns
        for dr in self.dish_returns:
            if dr.x <= x <= dr.x + dr.width and dr.y <= y <= dr.y + dr.height:
                return ("dish_return", dr)

        return (None, None)

    def handle_editor_click(self, pos, button):
        """Handle mouse click in editor mode"""
        if button == 1:  # Left click
            if self.current_tool in [EditorTool.STATION, EditorTool.WALL, EditorTool.DISH_RETURN]:
                self.drawing = True
                self.draw_start = pos
            elif self.current_tool == EditorTool.TABLE:
                self.tables.append(Table(x=pos[0], y=pos[1], seats=4))
            elif self.current_tool == EditorTool.ENTRANCE:
                self.entrances.append(Entrance(x=pos[0], y=pos[1]))
            elif self.current_tool == EditorTool.EXIT:
                self.exits.append(Exit(x=pos[0], y=pos[1]))

    def handle_editor_release(self, pos):
        """Handle mouse release in editor mode"""
        if not self.drawing or not self.draw_start:
            return

        x = min(self.draw_start[0], pos[0])
        y = min(self.draw_start[1], pos[1])
        w = abs(pos[0] - self.draw_start[0])
        h = abs(pos[1] - self.draw_start[1])

        if self.current_tool == EditorTool.STATION and w > 20 and h > 20:
            color = (random.randint(150, 255), random.randint(150, 255), random.randint(100, 200))
            station = Station(
                name=f"Station {len(self.stations) + 1}",
                x=x, y=y, width=w, height=h,
                color=color, food_type="all",
                service_time=6, capacity=3
            )
            self.stations.append(station)
            self.update_pathfinding()

        elif self.current_tool == EditorTool.WALL and (w > 5 or h > 5):
            wall = Wall(x1=self.draw_start[0], y1=self.draw_start[1],
                       x2=pos[0], y2=pos[1])
            self.walls.append(wall)
            self.update_pathfinding()

        elif self.current_tool == EditorTool.DISH_RETURN and w > 20 and h > 20:
            dr = DishReturn(x=x, y=y, width=w, height=h)
            self.dish_returns.append(dr)

        self.drawing = False
        self.draw_start = None

    def delete_at(self, pos):
        """Delete item at position"""
        item_type, item = self.get_item_at(pos)
        if item_type == "station":
            self.stations.remove(item)
        elif item_type == "table":
            self.tables.remove(item)
        elif item_type == "wall":
            self.walls.remove(item)
        elif item_type == "entrance":
            self.entrances.remove(item)
        elif item_type == "exit":
            self.exits.remove(item)
        elif item_type == "dish_return":
            self.dish_returns.remove(item)
        self.update_pathfinding()

    def reset_simulation(self):
        """Reset simulation state"""
        self.students = []
        self.student_id_counter = 0
        self.frame_count = 0
        self.total_students_served = 0
        self.total_wait_time = 0
        self.total_time_in_system = 0

        for station in self.stations:
            station.queue = []
            station.being_served = []
            station.service_timers = {}

        for table in self.tables:
            table.occupied_by = []

        for dr in self.dish_returns:
            dr.queue = []
            dr.being_served = []

        print("Simulation reset!")

    def clear_layout(self):
        """Clear all layout elements"""
        self.stations = []
        self.tables = []
        self.walls = []
        self.entrances = []
        self.exits = []
        self.dish_returns = []
        self.reset_simulation()
        self.update_pathfinding()
        print("Layout cleared!")

    def run(self):
        """Main loop"""
        print("=" * 60)
        print("DINING HALL FLOW SIMULATOR v2.0")
        print("=" * 60)
        print("Starting in EDITOR MODE - design your layout first!")
        print("Press SPACE to start simulation when ready.")
        print("=" * 60)

        while self.running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.running = False

                elif event.type == pygame.KEYDOWN:
                    if event.key in [pygame.K_ESCAPE, pygame.K_q]:
                        self.running = False

                    elif event.key == pygame.K_SPACE:
                        if self.editor_mode:
                            self.editor_mode = False
                            self.paused = False
                            self.update_pathfinding()
                            print("Simulation started!")
                        else:
                            self.paused = not self.paused

                    elif event.key == pygame.K_e:
                        self.editor_mode = not self.editor_mode
                        if self.editor_mode:
                            self.paused = True

                    elif event.key == pygame.K_s:
                        self.save_layout()

                    elif event.key == pygame.K_l and self.editor_mode:
                        self.load_background_image()

                    elif event.key == pygame.K_c and self.editor_mode:
                        self.clear_layout()

                    elif event.key == pygame.K_r:
                        self.reset_simulation()

                    elif event.key in [pygame.K_PLUS, pygame.K_EQUALS]:
                        self.speed = min(10.0, self.speed + 0.5)

                    elif event.key == pygame.K_MINUS:
                        self.speed = max(0.5, self.speed - 0.5)

                    elif event.key == pygame.K_DELETE and self.editor_mode:
                        pos = pygame.mouse.get_pos()
                        self.delete_at(pos)

                    # Tool selection
                    elif event.key == pygame.K_1 and self.editor_mode:
                        self.current_tool = EditorTool.STATION
                    elif event.key == pygame.K_2 and self.editor_mode:
                        self.current_tool = EditorTool.TABLE
                    elif event.key == pygame.K_3 and self.editor_mode:
                        self.current_tool = EditorTool.WALL
                    elif event.key == pygame.K_4 and self.editor_mode:
                        self.current_tool = EditorTool.ENTRANCE
                    elif event.key == pygame.K_5 and self.editor_mode:
                        self.current_tool = EditorTool.EXIT
                    elif event.key == pygame.K_6 and self.editor_mode:
                        self.current_tool = EditorTool.DISH_RETURN

                elif event.type == pygame.MOUSEBUTTONDOWN and self.editor_mode:
                    if event.pos[1] < WINDOW_HEIGHT - 60:  # Not on toolbar
                        self.handle_editor_click(event.pos, event.button)

                elif event.type == pygame.MOUSEBUTTONUP and self.editor_mode:
                    self.handle_editor_release(event.pos)

            self.update()
            self.draw()

            # Draw rectangle being drawn
            if self.editor_mode and self.drawing and self.draw_start:
                mouse = pygame.mouse.get_pos()
                x = min(self.draw_start[0], mouse[0])
                y = min(self.draw_start[1], mouse[1])
                w = abs(mouse[0] - self.draw_start[0])
                h = abs(mouse[1] - self.draw_start[1])
                pygame.draw.rect(self.screen, (255, 255, 100), (x, y, w, h), 2)
                pygame.display.flip()

            self.clock.tick(60)

        pygame.quit()


if __name__ == "__main__":
    sim = DiningHallSimulation()
    sim.run()
