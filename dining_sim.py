"""
Dining Hall Flow Simulator v2.5
================================
Agent-based simulation for analyzing dining hall bottlenecks.

Controls:
    SPACE      - Pause/Resume simulation
    E          - Toggle Editor mode
    +/-        - Speed up/slow down simulation
    [ / ]      - Decrease/increase spawn rate
    D          - Toggle debug pathfinding view
    F          - Force all students to recalculate routes
    R          - Reset simulation
    Q/ESC      - Quit

When Paused:
    Click on a student to see their stats

Editor Mode:
    0          - Select tool (click items to edit)
    1          - Station tool (click+drag to draw)
    2          - Table tool (click to place, then choose size)
    3          - Wall tool (click+drag to draw)
    4          - Entrance tool (click to place)
    5          - Exit tool (click to place)
    6          - Dish Return tool (click+drag)
    DELETE     - Delete item under cursor
    Ctrl+Z     - Undo
    Ctrl+Y     - Redo
    S          - Save layout
    L          - Load background image
    C          - Clear all
"""

import sys
import traceback

try:
    import pygame
    import json
    import random
    import math
    import heapq
    from pathlib import Path
    from enum import Enum
    from dataclasses import dataclass, field
    from typing import Optional, List, Tuple, Set
    import tkinter as tk
    from tkinter import filedialog
except ImportError as e:
    print("=" * 50)
    print(f"IMPORT ERROR: {e}")
    print("Make sure pygame is installed: pip install pygame")
    print("=" * 50)
    input("Press Enter to exit...")
    sys.exit(1)

# ============================================================================
# CONFIGURATION
# ============================================================================

WINDOW_WIDTH = 1500
WINDOW_HEIGHT = 950
PANEL_WIDTH = 280
GRID_SIZE = 8

STUDENT_RADIUS = 5
STUDENT_SPAWN_RATE_BASE = 120  # Base frames between spawns (higher = slower)
STUDENT_SPAWN_RATE_MIN = 10   # Minimum frames (fastest spawn)
STUDENT_SPAWN_RATE_MAX = 300  # Maximum frames (slowest spawn)
STUDENT_SPEED = 1.8
SEPARATION_RADIUS = 18
SEPARATION_FORCE = 1.5
WALL_AVOIDANCE_RADIUS = 20
WALL_AVOIDANCE_FORCE = 1.8
TABLE_AVOIDANCE_RADIUS = 16
QUEUE_SPACING = 22
APPROACH_SPREAD = 30  # How much to spread out approaching students

DIET_DISTRIBUTION = {
    "omnivore": 0.55,
    "vegetarian": 0.22,
    "vegan": 0.10,
    "allergen_sensitive": 0.08,
    "halal": 0.05
}

EAT_TIME_MIN = 400
EAT_TIME_MAX = 900
DISH_RETURN_TIME = 45
SERVICE_TIME_MULTIPLIER = 60

SECONDS_CHANCE = 0.18
DESSERT_CHANCE = 0.22
GROUP_CHANCE = 0.35  # Chance that a spawn is a group
GROUP_SIZE_MIN = 2
GROUP_SIZE_MAX = 4

COLORS = {
    "background": (25, 25, 30),
    "grid": (35, 35, 40),
    "wall": (70, 70, 80),
    "student_omnivore": (255, 220, 100),
    "student_vegetarian": (150, 255, 150),
    "student_vegan": (100, 255, 100),
    "student_allergen": (255, 180, 220),
    "student_halal": (180, 220, 255),
    "student_has_food": (180, 130, 80),
    "student_selected": (255, 255, 255),
    "table": (110, 75, 35),
    "table_occupied": (80, 50, 20),
    "dish_return": (100, 100, 120),
    "entrance": (80, 180, 80),
    "exit": (180, 80, 80),
    "flow_zone": (100, 100, 150, 80),
    "text": (255, 255, 255),
    "text_dark": (20, 20, 20),
    "text_muted": (150, 150, 150),
    "ui_bg": (20, 20, 25),
    "panel_bg": (30, 30, 38),
    "button": (55, 55, 65),
    "button_hover": (70, 70, 85),
    "button_active": (80, 100, 130),
    "slider_bg": (50, 50, 60),
    "slider_fill": (100, 140, 200),
    "checkbox_check": (100, 200, 100),
    "input_bg": (45, 45, 55),
    "selected": (255, 200, 100),
    "path_line": (100, 200, 255, 150),
    "group_ring": (255, 150, 255),
}

# Food categories - expanded
FOOD_CATEGORIES = [
    ("pizza", "Pizza", (255, 180, 100)),
    ("burgers", "Burgers/Grill", (200, 100, 80)),
    ("chicken", "Chicken", (255, 200, 150)),
    ("beef", "Beef", (180, 80, 80)),
    ("seafood", "Seafood", (100, 180, 220)),
    ("pork", "Pork", (255, 180, 180)),
    ("vegan", "Vegan", (100, 200, 100)),
    ("vegetarian", "Vegetarian", (150, 220, 150)),
    ("halal", "Halal", (150, 200, 255)),
    ("kosher", "Kosher", (200, 180, 255)),
    ("allergen_friendly", "Allergen Friendly", (200, 150, 255)),
    ("gluten_free", "Gluten Free", (255, 220, 180)),
    ("salad", "Salad Bar", (100, 180, 100)),
    ("asian", "Asian/Wok", (255, 150, 100)),
    ("mexican", "Mexican", (255, 200, 100)),
    ("italian", "Italian/Pasta", (255, 220, 180)),
    ("deli", "Deli/Sandwich", (220, 180, 140)),
    ("soup", "Soup", (180, 140, 100)),
    ("dessert", "Dessert", (255, 180, 200)),
    ("ice_cream", "Ice Cream", (200, 220, 255)),
    ("beverage", "Beverages", (150, 200, 255)),
    ("coffee", "Coffee/Tea", (180, 140, 100)),
    ("breakfast", "Breakfast", (255, 220, 150)),
    ("comfort", "Comfort Food", (220, 180, 140)),
]


# ============================================================================
# ENUMS AND DATA CLASSES
# ============================================================================

class StudentState(Enum):
    ENTERING = "entering"
    WALKING_TO_STATION = "walking"
    ENTERING_FLOW_ZONE = "entering_zone"
    IN_FLOW_ZONE = "in_flow"
    QUEUING = "queuing"
    BEING_SERVED = "being_served"
    WALKING_TO_TABLE = "to_table"
    EATING = "eating"
    WALKING_TO_DISH_RETURN = "to_dishes"
    QUEUING_DISH_RETURN = "dish_queue"
    RETURNING_DISHES = "returning"
    WALKING_TO_EXIT = "exiting"
    EXITED = "exited"


class DietType(Enum):
    OMNIVORE = "omnivore"
    VEGETARIAN = "vegetarian"
    VEGAN = "vegan"
    ALLERGEN_SENSITIVE = "allergen_sensitive"
    HALAL = "halal"


class EditorTool(Enum):
    SELECT = 0
    STATION = 1
    TABLE = 2
    WALL = 3
    ENTRANCE = 4
    EXIT = 5
    DISH_RETURN = 6


class TableShape(Enum):
    CIRCLE = "circle"
    SQUARE = "square"


@dataclass
class Station:
    name: str
    x: int
    y: int
    width: int
    height: int
    color: tuple
    food_categories: Set[str] = field(default_factory=lambda: {"pizza"})
    popularity: float = 0.5
    service_time: float = 6.0
    capacity: int = 1  # How many can be served at once
    queue: list = field(default_factory=list)
    being_served: list = field(default_factory=list)
    service_timers: dict = field(default_factory=dict)
    queue_direction: str = "down"

    # Flow-through zone settings
    is_flow_through: bool = False
    flow_entry_side: str = "left"
    flow_exit_side: str = "right"
    flow_positions: list = field(default_factory=list)

    @property
    def center(self):
        return (self.x + self.width // 2, self.y + self.height // 2)

    def get_flow_entry_point(self) -> Tuple[int, int]:
        if self.flow_entry_side == "left":
            return (self.x - 10, self.y + self.height // 2)
        elif self.flow_entry_side == "right":
            return (self.x + self.width + 10, self.y + self.height // 2)
        elif self.flow_entry_side == "top":
            return (self.x + self.width // 2, self.y - 10)
        else:
            return (self.x + self.width // 2, self.y + self.height + 10)

    def get_flow_exit_point(self) -> Tuple[int, int]:
        if self.flow_exit_side == "left":
            return (self.x - 10, self.y + self.height // 2)
        elif self.flow_exit_side == "right":
            return (self.x + self.width + 10, self.y + self.height // 2)
        elif self.flow_exit_side == "top":
            return (self.x + self.width // 2, self.y - 10)
        else:
            return (self.x + self.width // 2, self.y + self.height + 10)

    def get_flow_path(self, num_points: int = 5) -> List[Tuple[int, int]]:
        entry = self.get_flow_entry_point()
        exit_pt = self.get_flow_exit_point()
        path = []
        for i in range(num_points):
            t = i / (num_points - 1)
            px = entry[0] + (exit_pt[0] - entry[0]) * t
            py = entry[1] + (exit_pt[1] - entry[1]) * t
            path.append((int(px), int(py)))
        return path

    def get_service_point(self) -> Tuple[int, int]:
        """The point where a student stands to be served"""
        if self.queue_direction == "down":
            return (self.x + self.width // 2, self.y + self.height + 15)
        elif self.queue_direction == "up":
            return (self.x + self.width // 2, self.y - 15)
        elif self.queue_direction == "left":
            return (self.x - 15, self.y + self.height // 2)
        else:
            return (self.x + self.width + 15, self.y + self.height // 2)

    def get_queue_position(self, index: int, walls: list = None) -> Tuple[int, int]:
        """Get position for person at index in queue (0 = being served)"""
        service_pt = self.get_service_point()
        if index == 0:
            return service_pt

        # Direction vector for queue
        dx, dy = 0, 0
        if self.queue_direction == "down":
            dy = 1
        elif self.queue_direction == "up":
            dy = -1
        elif self.queue_direction == "left":
            dx = -1
        else:
            dx = 1

        # Calculate position
        px = service_pt[0] + dx * index * QUEUE_SPACING
        py = service_pt[1] + dy * index * QUEUE_SPACING

        return (int(px), int(py))

    def can_serve_diet(self, diet: DietType) -> bool:
        if diet == DietType.VEGAN:
            return "vegan" in self.food_categories
        elif diet == DietType.VEGETARIAN:
            return any(cat in self.food_categories for cat in
                      ["vegan", "vegetarian", "salad", "soup", "dessert", "beverage", "ice_cream", "coffee"])
        elif diet == DietType.ALLERGEN_SENSITIVE:
            return "allergen_friendly" in self.food_categories or "gluten_free" in self.food_categories
        elif diet == DietType.HALAL:
            return "halal" in self.food_categories or "vegan" in self.food_categories or "seafood" in self.food_categories
        else:
            return len(self.food_categories) > 0

    def is_dessert_station(self) -> bool:
        dessert_cats = {"dessert", "ice_cream"}
        return bool(self.food_categories & dessert_cats) and len(self.food_categories - dessert_cats) == 0


@dataclass
class Table:
    x: int
    y: int
    seats: int = 4
    shape: str = "circle"
    occupied_by: list = field(default_factory=list)

    @property
    def center(self):
        return (self.x, self.y)

    @property
    def has_space(self):
        return len(self.occupied_by) < self.seats

    @property
    def radius(self):
        if self.seats <= 2:
            return 14
        elif self.seats <= 4:
            return 17
        else:
            return 21

    def get_rect(self) -> pygame.Rect:
        r = self.radius
        return pygame.Rect(self.x - r, self.y - r, r * 2, r * 2)

    def get_seat_positions(self) -> List[Tuple[int, int]]:
        positions = []
        seat_radius = self.radius + 8
        for i in range(self.seats):
            angle = (2 * math.pi * i) / self.seats - math.pi / 2
            px = self.x + int(seat_radius * math.cos(angle))
            py = self.y + int(seat_radius * math.sin(angle))
            positions.append((px, py))
        return positions


@dataclass
class Wall:
    x1: int
    y1: int
    x2: int
    y2: int
    thickness: int = 6

    def get_rect(self) -> pygame.Rect:
        x = min(self.x1, self.x2)
        y = min(self.y1, self.y2)
        w = max(abs(self.x2 - self.x1), self.thickness)
        h = max(abs(self.y2 - self.y1), self.thickness)
        return pygame.Rect(x, y, w, h)

    def get_expanded_rect(self, margin: int) -> pygame.Rect:
        return self.get_rect().inflate(margin * 2, margin * 2)


@dataclass
class DishReturn:
    x: int
    y: int
    width: int
    height: int
    queue: list = field(default_factory=list)
    being_served: list = field(default_factory=list)
    capacity: int = 1
    queue_direction: str = "down"

    @property
    def center(self):
        return (self.x + self.width // 2, self.y + self.height // 2)

    def get_service_point(self) -> Tuple[int, int]:
        if self.queue_direction == "down":
            return (self.x + self.width // 2, self.y + self.height + 15)
        elif self.queue_direction == "up":
            return (self.x + self.width // 2, self.y - 15)
        elif self.queue_direction == "left":
            return (self.x - 15, self.y + self.height // 2)
        else:
            return (self.x + self.width + 15, self.y + self.height // 2)

    def get_queue_position(self, index: int) -> Tuple[int, int]:
        service_pt = self.get_service_point()
        if index == 0:
            return service_pt

        dx, dy = 0, 0
        if self.queue_direction == "down":
            dy = 1
        elif self.queue_direction == "up":
            dy = -1
        elif self.queue_direction == "left":
            dx = -1
        else:
            dx = 1

        px = service_pt[0] + dx * index * QUEUE_SPACING
        py = service_pt[1] + dy * index * QUEUE_SPACING
        return (int(px), int(py))


@dataclass
class Entrance:
    x: int
    y: int
    spawn_rate: int = STUDENT_SPAWN_RATE_BASE

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
    target_dish_return: DishReturn = None
    seat_position: tuple = None
    queue_position: int = -1
    speed: float = STUDENT_SPEED
    eat_timer: int = 0
    has_food: bool = False
    has_dessert: bool = False  # Track if they got dessert
    meals_eaten: int = 0
    time_in_system: int = 0
    wait_time: int = 0
    vx: float = 0
    vy: float = 0
    stuck_timer: int = 0
    flow_progress: int = 0
    stations_visited: list = field(default_factory=list)  # Track visited stations
    group_id: int = -1  # -1 means solo, otherwise group identifier

    @property
    def color(self):
        colors = {
            DietType.VEGAN: COLORS["student_vegan"],
            DietType.VEGETARIAN: COLORS["student_vegetarian"],
            DietType.ALLERGEN_SENSITIVE: COLORS["student_allergen"],
            DietType.HALAL: COLORS["student_halal"],
        }
        return colors.get(self.diet, COLORS["student_omnivore"])

    @property
    def pos(self):
        return (self.x, self.y)

    def get_state_description(self) -> str:
        descriptions = {
            StudentState.ENTERING: "Just entered",
            StudentState.WALKING_TO_STATION: f"Walking to {self.target_station.name if self.target_station else 'station'}",
            StudentState.IN_FLOW_ZONE: f"In flow zone at {self.target_station.name if self.target_station else 'station'}",
            StudentState.QUEUING: f"Waiting in queue at {self.target_station.name if self.target_station else 'station'}",
            StudentState.BEING_SERVED: f"Being served at {self.target_station.name if self.target_station else 'station'}",
            StudentState.WALKING_TO_TABLE: "Finding a table",
            StudentState.EATING: "Eating",
            StudentState.WALKING_TO_DISH_RETURN: "Going to return dishes",
            StudentState.QUEUING_DISH_RETURN: "Waiting to return dishes",
            StudentState.RETURNING_DISHES: "Returning dishes",
            StudentState.WALKING_TO_EXIT: "Leaving",
            StudentState.EXITED: "Left the venue",
        }
        return descriptions.get(self.state, str(self.state.value))


# ============================================================================
# UI COMPONENTS
# ============================================================================

class Slider:
    def __init__(self, x, y, width, min_val, max_val, value, label, format_str="{:.1f}"):
        self.rect = pygame.Rect(x, y, width, 18)
        self.min_val = min_val
        self.max_val = max_val
        self.value = value
        self.label = label
        self.format_str = format_str
        self.dragging = False

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEBUTTONDOWN and self.rect.collidepoint(event.pos):
            self.dragging = True
            self._update_value(event.pos[0])
            return True
        elif event.type == pygame.MOUSEBUTTONUP:
            self.dragging = False
        elif event.type == pygame.MOUSEMOTION and self.dragging:
            self._update_value(event.pos[0])
            return True
        return False

    def _update_value(self, mouse_x):
        ratio = max(0, min(1, (mouse_x - self.rect.x) / self.rect.width))
        self.value = self.min_val + ratio * (self.max_val - self.min_val)

    def draw(self, screen, font):
        label_text = font.render(f"{self.label}: {self.format_str.format(self.value)}", True, COLORS["text"])
        screen.blit(label_text, (self.rect.x, self.rect.y - 16))
        pygame.draw.rect(screen, COLORS["slider_bg"], self.rect, border_radius=3)
        fill_width = int((self.value - self.min_val) / (self.max_val - self.min_val) * self.rect.width)
        pygame.draw.rect(screen, COLORS["slider_fill"],
                        pygame.Rect(self.rect.x, self.rect.y, fill_width, self.rect.height), border_radius=3)
        pygame.draw.circle(screen, COLORS["text"], (self.rect.x + fill_width, self.rect.centery), 7)


class Checkbox:
    def __init__(self, x, y, label, checked=False, color=None):
        self.rect = pygame.Rect(x, y, 16, 16)
        self.label = label
        self.checked = checked
        self.color = color or COLORS["checkbox_check"]

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEBUTTONDOWN:
            click_area = pygame.Rect(self.rect.x, self.rect.y, 220, self.rect.height)
            if click_area.collidepoint(event.pos):
                self.checked = not self.checked
                return True
        return False

    def draw(self, screen, font):
        pygame.draw.rect(screen, COLORS["input_bg"], self.rect)
        pygame.draw.rect(screen, COLORS["text_muted"], self.rect, 1)
        if self.checked:
            pygame.draw.rect(screen, self.color, self.rect.inflate(-5, -5))
        screen.blit(font.render(self.label, True, COLORS["text"]), (self.rect.right + 6, self.rect.y))


class TextInput:
    def __init__(self, x, y, width, value="", label=""):
        self.rect = pygame.Rect(x, y, width, 24)
        self.value = value
        self.label = label
        self.active = False

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEBUTTONDOWN:
            self.active = self.rect.collidepoint(event.pos)
            return self.active
        elif event.type == pygame.KEYDOWN and self.active:
            if event.key == pygame.K_BACKSPACE:
                self.value = self.value[:-1]
            elif event.key == pygame.K_RETURN:
                self.active = False
            elif event.unicode.isprintable() and len(self.value) < 20:
                self.value += event.unicode
            return True
        return False

    def draw(self, screen, font):
        if self.label:
            screen.blit(font.render(self.label, True, COLORS["text"]), (self.rect.x, self.rect.y - 16))
        pygame.draw.rect(screen, COLORS["button_active"] if self.active else COLORS["input_bg"],
                        self.rect, border_radius=3)
        pygame.draw.rect(screen, COLORS["text_muted"], self.rect, 1, border_radius=3)
        screen.blit(font.render(self.value, True, COLORS["text"]), (self.rect.x + 5, self.rect.y + 4))


class Button:
    def __init__(self, x, y, width, height, label, color=None):
        self.rect = pygame.Rect(x, y, width, height)
        self.label = label
        self.color = color or COLORS["button"]
        self.hovered = False

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEMOTION:
            self.hovered = self.rect.collidepoint(event.pos)
        elif event.type == pygame.MOUSEBUTTONDOWN and self.rect.collidepoint(event.pos):
            return True
        return False

    def draw(self, screen, font):
        pygame.draw.rect(screen, COLORS["button_hover"] if self.hovered else self.color,
                        self.rect, border_radius=4)
        pygame.draw.rect(screen, COLORS["text_muted"], self.rect, 1, border_radius=4)
        text = font.render(self.label, True, COLORS["text"])
        screen.blit(text, text.get_rect(center=self.rect.center))


# ============================================================================
# PATHFINDING
# ============================================================================

class Pathfinder:
    def __init__(self, width, height, grid_size):
        self.width = width
        self.height = height
        self.grid_size = grid_size
        self.cols = width // grid_size
        self.rows = height // grid_size
        self.obstacles = set()
        self.high_cost = set()

    def update_obstacles(self, walls: List[Wall], stations: List[Station], tables: List[Table]):
        self.obstacles.clear()
        self.high_cost.clear()
        margin = 2

        for wall in walls:
            rect = wall.get_rect()
            for gx in range(rect.left // self.grid_size - margin, (rect.right // self.grid_size) + margin + 1):
                for gy in range(rect.top // self.grid_size - margin, (rect.bottom // self.grid_size) + margin + 1):
                    if 0 <= gx < self.cols and 0 <= gy < self.rows:
                        if (rect.left // self.grid_size <= gx <= rect.right // self.grid_size and
                            rect.top // self.grid_size <= gy <= rect.bottom // self.grid_size):
                            self.obstacles.add((gx, gy))
                        else:
                            self.high_cost.add((gx, gy))

        for station in stations:
            for gx in range(station.x // self.grid_size, (station.x + station.width) // self.grid_size + 1):
                for gy in range(station.y // self.grid_size, (station.y + station.height) // self.grid_size + 1):
                    if 0 <= gx < self.cols and 0 <= gy < self.rows:
                        self.obstacles.add((gx, gy))

        for table in tables:
            rect = table.get_rect()
            for gx in range(rect.left // self.grid_size - 1, (rect.right // self.grid_size) + 2):
                for gy in range(rect.top // self.grid_size - 1, (rect.bottom // self.grid_size) + 2):
                    if 0 <= gx < self.cols and 0 <= gy < self.rows:
                        self.obstacles.add((gx, gy))

    def find_path(self, start, goal) -> List[Tuple[int, int]]:
        start_grid = (int(start[0] // self.grid_size), int(start[1] // self.grid_size))
        goal_grid = (int(goal[0] // self.grid_size), int(goal[1] // self.grid_size))
        start_grid = (max(0, min(start_grid[0], self.cols-1)), max(0, min(start_grid[1], self.rows-1)))
        goal_grid = (max(0, min(goal_grid[0], self.cols-1)), max(0, min(goal_grid[1], self.rows-1)))

        if start_grid in self.obstacles:
            start_grid = self._find_nearest_free(start_grid)
        if goal_grid in self.obstacles:
            goal_grid = self._find_nearest_free(goal_grid)
        if not start_grid or not goal_grid:
            return [goal]

        frontier = [(0, start_grid)]
        came_from = {start_grid: None}
        cost_so_far = {start_grid: 0}

        while frontier:
            _, current = heapq.heappop(frontier)
            if current == goal_grid:
                break

            for dx, dy in [(0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)]:
                nx, ny = current[0] + dx, current[1] + dy
                if 0 <= nx < self.cols and 0 <= ny < self.rows and (nx, ny) not in self.obstacles:
                    move_cost = 1.4 if abs(dx) + abs(dy) == 2 else 1.0
                    if (nx, ny) in self.high_cost:
                        move_cost += 3.0
                    new_cost = cost_so_far[current] + move_cost
                    if (nx, ny) not in cost_so_far or new_cost < cost_so_far[(nx, ny)]:
                        cost_so_far[(nx, ny)] = new_cost
                        priority = new_cost + math.sqrt((nx - goal_grid[0])**2 + (ny - goal_grid[1])**2)
                        heapq.heappush(frontier, (priority, (nx, ny)))
                        came_from[(nx, ny)] = current

        if goal_grid not in came_from:
            return [goal]

        path = []
        current = goal_grid
        while current:
            path.append((current[0] * self.grid_size + self.grid_size // 2,
                        current[1] * self.grid_size + self.grid_size // 2))
            current = came_from[current]
        path.reverse()
        path.append(goal)
        return path[1:] if len(path) > 1 else [goal]

    def _find_nearest_free(self, pos):
        for r in range(1, 30):
            for dx in range(-r, r + 1):
                for dy in range(-r, r + 1):
                    check = (pos[0] + dx, pos[1] + dy)
                    if 0 <= check[0] < self.cols and 0 <= check[1] < self.rows and check not in self.obstacles:
                        return check
        return None


# ============================================================================
# PROPERTIES PANELS
# ============================================================================

class StationPropertiesPanel:
    def __init__(self, x, y, width, height):
        self.rect = pygame.Rect(x, y, width, height)
        self.visible = False
        self.station = None
        self.scroll_y = 0
        self.max_scroll = 0
        self.font = None
        self.small_font = None
        self.elements = {}
        self.food_scroll_y = 0
        self.food_scroll_max = 0
        self.food_area_rect = None

    def init_fonts(self, font, small_font):
        self.font = font
        self.small_font = small_font

    def show(self, station):
        self.station = station
        self.visible = True
        self.scroll_y = 0
        self.food_scroll_y = 0
        self._create_elements()

    def hide(self):
        self.visible = False
        self.station = None

    def _create_elements(self):
        if not self.station:
            return
        x, w = self.rect.x + 12, self.rect.width - 24
        y = self.rect.y + 45

        self.elements = {
            "name": TextInput(x, y, w, self.station.name, "Station Name"),
            "popularity": Slider(x, y + 50, w, 0, 1, self.station.popularity, "Popularity", "{:.0%}"),
            "service_time": Slider(x, y + 95, w, 1, 20, self.station.service_time, "Service Time (sec)"),
            "capacity": Slider(x, y + 140, w, 1, 6, self.station.capacity, "Serve at once", "{:.0f}"),
        }

        # Queue direction buttons
        btn_w = (w - 9) // 4
        y_btn = y + 175
        self.elements["q_up"] = Button(x, y_btn, btn_w, 24, "Up")
        self.elements["q_down"] = Button(x + btn_w + 3, y_btn, btn_w, 24, "Down")
        self.elements["q_left"] = Button(x + (btn_w + 3) * 2, y_btn, btn_w, 24, "Left")
        self.elements["q_right"] = Button(x + (btn_w + 3) * 3, y_btn, btn_w, 24, "Right")

        # Flow-through toggle
        y_flow = y + 210
        self.elements["flow_through"] = Checkbox(x, y_flow, "Flow-Through Zone", self.station.is_flow_through)

        # Flow direction
        y_flow_dir = y + 235
        self.elements["flow_entry_label"] = ("label", "Entry Side:", x, y_flow_dir)
        btn_w2 = (w - 9) // 4
        self.elements["fe_left"] = Button(x, y_flow_dir + 18, btn_w2, 22, "Left")
        self.elements["fe_right"] = Button(x + btn_w2 + 3, y_flow_dir + 18, btn_w2, 22, "Right")
        self.elements["fe_top"] = Button(x + (btn_w2 + 3) * 2, y_flow_dir + 18, btn_w2, 22, "Top")
        self.elements["fe_bottom"] = Button(x + (btn_w2 + 3) * 3, y_flow_dir + 18, btn_w2, 22, "Btm")

        y_flow_exit = y_flow_dir + 50
        self.elements["flow_exit_label"] = ("label", "Exit Side:", x, y_flow_exit)
        self.elements["fx_left"] = Button(x, y_flow_exit + 18, btn_w2, 22, "Left")
        self.elements["fx_right"] = Button(x + btn_w2 + 3, y_flow_exit + 18, btn_w2, 22, "Right")
        self.elements["fx_top"] = Button(x + (btn_w2 + 3) * 2, y_flow_exit + 18, btn_w2, 22, "Top")
        self.elements["fx_bottom"] = Button(x + (btn_w2 + 3) * 3, y_flow_exit + 18, btn_w2, 22, "Btm")

        # Food categories with scroll area
        y_cat = y_flow_exit + 55
        self.elements["cat_label"] = ("label", "Food Categories:", x, y_cat)

        # Scrollable food area
        self.food_area_rect = pygame.Rect(x, y_cat + 18, w, 200)
        self.food_scroll_max = max(0, len(FOOD_CATEGORIES) * 22 - 200)

        self.elements["food_checkboxes"] = []
        for i, (cat_id, cat_name, cat_color) in enumerate(FOOD_CATEGORIES):
            cb = Checkbox(x + 5, y_cat + 18 + i * 22, cat_name, cat_id in self.station.food_categories, cat_color)
            cb.category_id = cat_id
            cb.base_y = y_cat + 18 + i * 22
            self.elements["food_checkboxes"].append(cb)

        self.elements["close"] = Button(x, y_cat + 230, w, 28, "Close")

    def handle_event(self, event) -> bool:
        if not self.visible or not self.station:
            return False

        if event.type == pygame.MOUSEBUTTONDOWN and not self.rect.collidepoint(event.pos):
            return False

        # Scroll food categories
        if event.type == pygame.MOUSEWHEEL:
            mouse_pos = pygame.mouse.get_pos()
            if self.food_area_rect and self.food_area_rect.collidepoint(mouse_pos):
                self.food_scroll_y = max(0, min(self.food_scroll_max, self.food_scroll_y - event.y * 25))
                # Update checkbox positions
                for cb in self.elements.get("food_checkboxes", []):
                    cb.rect.y = cb.base_y - self.food_scroll_y
                return True

        e = self.elements
        if isinstance(e.get("name"), TextInput) and e["name"].handle_event(event):
            self.station.name = e["name"].value
            return True
        if isinstance(e.get("popularity"), Slider) and e["popularity"].handle_event(event):
            self.station.popularity = e["popularity"].value
            return True
        if isinstance(e.get("service_time"), Slider) and e["service_time"].handle_event(event):
            self.station.service_time = e["service_time"].value
            return True
        if isinstance(e.get("capacity"), Slider) and e["capacity"].handle_event(event):
            self.station.capacity = int(e["capacity"].value)
            return True

        for key, direction in [("q_up", "up"), ("q_down", "down"), ("q_left", "left"), ("q_right", "right")]:
            if isinstance(e.get(key), Button) and e[key].handle_event(event):
                self.station.queue_direction = direction
                return True

        if isinstance(e.get("flow_through"), Checkbox) and e["flow_through"].handle_event(event):
            self.station.is_flow_through = e["flow_through"].checked
            return True

        for key, side in [("fe_left", "left"), ("fe_right", "right"), ("fe_top", "top"), ("fe_bottom", "bottom")]:
            if isinstance(e.get(key), Button) and e[key].handle_event(event):
                self.station.flow_entry_side = side
                return True
        for key, side in [("fx_left", "left"), ("fx_right", "right"), ("fx_top", "top"), ("fx_bottom", "bottom")]:
            if isinstance(e.get(key), Button) and e[key].handle_event(event):
                self.station.flow_exit_side = side
                return True

        # Food checkboxes - only handle if in visible area
        for cb in e.get("food_checkboxes", []):
            if self.food_area_rect and self.food_area_rect.colliderect(cb.rect):
                if cb.handle_event(event):
                    if cb.checked:
                        self.station.food_categories.add(cb.category_id)
                    else:
                        self.station.food_categories.discard(cb.category_id)
                    return True

        if isinstance(e.get("close"), Button) and e["close"].handle_event(event):
            self.hide()
            return True

        return self.rect.collidepoint(pygame.mouse.get_pos())

    def draw(self, screen):
        if not self.visible:
            return
        pygame.draw.rect(screen, COLORS["panel_bg"], self.rect)
        pygame.draw.line(screen, COLORS["text_muted"], (self.rect.x, 0), (self.rect.x, WINDOW_HEIGHT))

        screen.blit(self.font.render("Station Properties", True, COLORS["text"]), (self.rect.x + 12, self.rect.y + 12))

        e = self.elements
        for key, val in e.items():
            if key == "food_checkboxes":
                continue
            if isinstance(val, tuple) and val[0] == "label":
                screen.blit(self.small_font.render(val[1], True, COLORS["text"]), (val[2], val[3]))
            elif isinstance(val, (Slider, Checkbox, TextInput, Button)):
                if isinstance(val, Button) and key.startswith("q_"):
                    val.color = COLORS["button_active"] if self.station.queue_direction == key[2:] else COLORS["button"]
                elif isinstance(val, Button) and key.startswith("fe_"):
                    val.color = COLORS["button_active"] if self.station.flow_entry_side == key[3:] else COLORS["button"]
                elif isinstance(val, Button) and key.startswith("fx_"):
                    val.color = COLORS["button_active"] if self.station.flow_exit_side == key[3:] else COLORS["button"]
                val.draw(screen, self.small_font)

        # Draw scrollable food area with clipping
        if self.food_area_rect:
            pygame.draw.rect(screen, COLORS["input_bg"], self.food_area_rect)
            # Create clip rect
            old_clip = screen.get_clip()
            screen.set_clip(self.food_area_rect)
            for cb in e.get("food_checkboxes", []):
                cb.draw(screen, self.small_font)
            screen.set_clip(old_clip)

            # Draw scroll indicator
            if self.food_scroll_max > 0:
                scroll_height = max(20, 200 * 200 // (200 + self.food_scroll_max))
                scroll_y = self.food_area_rect.y + (self.food_scroll_y / self.food_scroll_max) * (200 - scroll_height)
                pygame.draw.rect(screen, COLORS["slider_fill"],
                               (self.food_area_rect.right - 8, scroll_y, 6, scroll_height), border_radius=3)


class TablePropertiesPanel:
    def __init__(self, x, y, width, height):
        self.rect = pygame.Rect(x, y, width, height)
        self.visible = False
        self.table = None
        self.font = None
        self.small_font = None
        self.elements = {}

    def init_fonts(self, font, small_font):
        self.font = font
        self.small_font = small_font

    def show(self, table):
        self.table = table
        self.visible = True
        self._create_elements()

    def hide(self):
        self.visible = False
        self.table = None

    def _create_elements(self):
        if not self.table:
            return
        x, w = self.rect.x + 12, self.rect.width - 24
        y = self.rect.y + 45

        btn_w = (w - 6) // 3
        self.elements = {
            "seats_label": ("label", "Seats:", x, y),
            "seats_2": Button(x, y + 18, btn_w, 26, "2"),
            "seats_4": Button(x + btn_w + 3, y + 18, btn_w, 26, "4"),
            "seats_6": Button(x + (btn_w + 3) * 2, y + 18, btn_w, 26, "6"),
            "shape_label": ("label", "Shape:", x, y + 60),
            "shape_circle": Button(x, y + 78, w // 2 - 2, 26, "Circle"),
            "shape_square": Button(x + w // 2 + 2, y + 78, w // 2 - 2, 26, "Square"),
            "close": Button(x, y + 120, w, 28, "Close"),
        }

    def handle_event(self, event) -> bool:
        if not self.visible or not self.table:
            return False
        if event.type == pygame.MOUSEBUTTONDOWN and not self.rect.collidepoint(event.pos):
            return False

        e = self.elements
        for key, seats in [("seats_2", 2), ("seats_4", 4), ("seats_6", 6)]:
            if isinstance(e.get(key), Button) and e[key].handle_event(event):
                self.table.seats = seats
                return True

        for key, shape in [("shape_circle", "circle"), ("shape_square", "square")]:
            if isinstance(e.get(key), Button) and e[key].handle_event(event):
                self.table.shape = shape
                return True

        if isinstance(e.get("close"), Button) and e["close"].handle_event(event):
            self.hide()
            return True

        return self.rect.collidepoint(pygame.mouse.get_pos())

    def draw(self, screen):
        if not self.visible:
            return
        pygame.draw.rect(screen, COLORS["panel_bg"], self.rect)
        pygame.draw.line(screen, COLORS["text_muted"], (self.rect.x, 0), (self.rect.x, WINDOW_HEIGHT))
        screen.blit(self.font.render("Table Properties", True, COLORS["text"]), (self.rect.x + 12, self.rect.y + 12))

        e = self.elements
        for key, val in e.items():
            if isinstance(val, tuple) and val[0] == "label":
                screen.blit(self.small_font.render(val[1], True, COLORS["text"]), (val[2], val[3]))
            elif isinstance(val, Button):
                if key.startswith("seats_") and self.table.seats == int(key[-1]):
                    val.color = COLORS["button_active"]
                elif key.startswith("shape_") and self.table.shape == key[6:]:
                    val.color = COLORS["button_active"]
                else:
                    val.color = COLORS["button"]
                val.draw(screen, self.small_font)


class DishReturnPropertiesPanel:
    def __init__(self, x, y, width, height):
        self.rect = pygame.Rect(x, y, width, height)
        self.visible = False
        self.dish_return = None
        self.font = None
        self.small_font = None
        self.elements = {}

    def init_fonts(self, font, small_font):
        self.font = font
        self.small_font = small_font

    def show(self, dish_return):
        self.dish_return = dish_return
        self.visible = True
        self._create_elements()

    def hide(self):
        self.visible = False
        self.dish_return = None

    def _create_elements(self):
        if not self.dish_return:
            return
        x, w = self.rect.x + 12, self.rect.width - 24
        y = self.rect.y + 45

        btn_w = (w - 9) // 4
        self.elements = {
            "capacity": Slider(x, y, w, 1, 4, self.dish_return.capacity, "Capacity", "{:.0f}"),
            "dir_label": ("label", "Queue Direction:", x, y + 45),
            "q_up": Button(x, y + 63, btn_w, 24, "Up"),
            "q_down": Button(x + btn_w + 3, y + 63, btn_w, 24, "Down"),
            "q_left": Button(x + (btn_w + 3) * 2, y + 63, btn_w, 24, "Left"),
            "q_right": Button(x + (btn_w + 3) * 3, y + 63, btn_w, 24, "Right"),
            "close": Button(x, y + 105, w, 28, "Close"),
        }

    def handle_event(self, event) -> bool:
        if not self.visible or not self.dish_return:
            return False
        if event.type == pygame.MOUSEBUTTONDOWN and not self.rect.collidepoint(event.pos):
            return False

        e = self.elements
        if isinstance(e.get("capacity"), Slider) and e["capacity"].handle_event(event):
            self.dish_return.capacity = int(e["capacity"].value)
            return True

        for key, direction in [("q_up", "up"), ("q_down", "down"), ("q_left", "left"), ("q_right", "right")]:
            if isinstance(e.get(key), Button) and e[key].handle_event(event):
                self.dish_return.queue_direction = direction
                return True

        if isinstance(e.get("close"), Button) and e["close"].handle_event(event):
            self.hide()
            return True

        return self.rect.collidepoint(pygame.mouse.get_pos())

    def draw(self, screen):
        if not self.visible:
            return
        pygame.draw.rect(screen, COLORS["panel_bg"], self.rect)
        pygame.draw.line(screen, COLORS["text_muted"], (self.rect.x, 0), (self.rect.x, WINDOW_HEIGHT))
        screen.blit(self.font.render("Dish Return", True, COLORS["text"]), (self.rect.x + 12, self.rect.y + 12))

        e = self.elements
        for key, val in e.items():
            if isinstance(val, tuple) and val[0] == "label":
                screen.blit(self.small_font.render(val[1], True, COLORS["text"]), (val[2], val[3]))
            elif isinstance(val, (Slider, Button)):
                if isinstance(val, Button) and key.startswith("q_"):
                    val.color = COLORS["button_active"] if self.dish_return.queue_direction == key[2:] else COLORS["button"]
                val.draw(screen, self.small_font)


class StudentInfoPanel:
    def __init__(self, x, y, width, height):
        self.rect = pygame.Rect(x, y, width, height)
        self.visible = False
        self.student = None
        self.font = None
        self.small_font = None

    def init_fonts(self, font, small_font):
        self.font = font
        self.small_font = small_font

    def show(self, student):
        self.student = student
        self.visible = True

    def hide(self):
        self.visible = False
        self.student = None

    def draw(self, screen):
        if not self.visible or not self.student:
            return

        pygame.draw.rect(screen, COLORS["panel_bg"], self.rect)
        pygame.draw.rect(screen, COLORS["selected"], self.rect, 2)

        s = self.student
        y = self.rect.y + 12
        x = self.rect.x + 12

        screen.blit(self.font.render(f"Student #{s.id}", True, COLORS["text"]), (x, y))
        y += 25

        # Diet with color
        diet_colors = {
            DietType.OMNIVORE: COLORS["student_omnivore"],
            DietType.VEGETARIAN: COLORS["student_vegetarian"],
            DietType.VEGAN: COLORS["student_vegan"],
            DietType.ALLERGEN_SENSITIVE: COLORS["student_allergen"],
            DietType.HALAL: COLORS["student_halal"],
        }
        pygame.draw.circle(screen, diet_colors.get(s.diet, COLORS["text"]), (x + 8, y + 7), 6)
        screen.blit(self.small_font.render(f"Diet: {s.diet.value.replace('_', ' ').title()}", True, COLORS["text"]), (x + 20, y))
        y += 20

        # Current state
        screen.blit(self.small_font.render(f"Status: {s.get_state_description()}", True, COLORS["text"]), (x, y))
        y += 20

        # Has food?
        food_status = "Has dessert" if s.has_dessert else ("Has food" if s.has_food else "No food yet")
        screen.blit(self.small_font.render(f"Food: {food_status}", True, COLORS["text"]), (x, y))
        y += 20

        # Group info
        if s.group_id >= 0:
            pygame.draw.circle(screen, COLORS["group_ring"], (x + 8, y + 7), 6, 2)
            screen.blit(self.small_font.render(f"Group #{s.group_id}", True, COLORS["text"]), (x + 20, y))
            y += 20

        # Time stats
        screen.blit(self.small_font.render(f"Time in system: {s.time_in_system // 60}s", True, COLORS["text"]), (x, y))
        y += 18
        screen.blit(self.small_font.render(f"Wait time: {s.wait_time // 60}s", True, COLORS["text"]), (x, y))
        y += 25

        # Stations visited
        screen.blit(self.small_font.render("Stations visited:", True, COLORS["text"]), (x, y))
        y += 18
        if s.stations_visited:
            for station_name in s.stations_visited[-5:]:  # Last 5
                screen.blit(self.small_font.render(f"  - {station_name}", True, COLORS["text_muted"]), (x, y))
                y += 16
        else:
            screen.blit(self.small_font.render("  (none yet)", True, COLORS["text_muted"]), (x, y))


# ============================================================================
# MAIN SIMULATION
# ============================================================================

class DiningHallSimulation:
    def __init__(self):
        pygame.init()
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        pygame.display.set_caption("Dining Hall Flow Simulator v2.5")
        self.clock = pygame.time.Clock()
        self.font = pygame.font.Font(None, 24)
        self.small_font = pygame.font.Font(None, 18)

        self.play_area = pygame.Rect(0, 0, WINDOW_WIDTH - PANEL_WIDTH, WINDOW_HEIGHT)
        self.running = True
        self.paused = True
        self.speed = 1.0
        self.spawn_rate = STUDENT_SPAWN_RATE_BASE  # Frames between spawns
        self.frame_count = 0
        self.student_id_counter = 0

        self.editor_mode = True
        self.current_tool = EditorTool.SELECT
        self.drawing = False
        self.draw_start = None

        self.stations: List[Station] = []
        self.tables: List[Table] = []
        self.walls: List[Wall] = []
        self.entrances: List[Entrance] = []
        self.exits: List[Exit] = []
        self.dish_returns: List[DishReturn] = []
        self.students: List[Student] = []

        self.pathfinder = Pathfinder(self.play_area.width, WINDOW_HEIGHT, GRID_SIZE)
        self.background_image = None
        self.background_path = None

        self.total_students_served = 0
        self.total_wait_time = 0
        self.total_time_in_system = 0

        # Panels
        self.station_panel = StationPropertiesPanel(WINDOW_WIDTH - PANEL_WIDTH, 0, PANEL_WIDTH, WINDOW_HEIGHT)
        self.station_panel.init_fonts(self.font, self.small_font)
        self.table_panel = TablePropertiesPanel(WINDOW_WIDTH - PANEL_WIDTH, 0, PANEL_WIDTH, WINDOW_HEIGHT)
        self.table_panel.init_fonts(self.font, self.small_font)
        self.dish_panel = DishReturnPropertiesPanel(WINDOW_WIDTH - PANEL_WIDTH, 0, PANEL_WIDTH, WINDOW_HEIGHT)
        self.dish_panel.init_fonts(self.font, self.small_font)
        self.student_panel = StudentInfoPanel(10, 170, 220, 240)
        self.student_panel.init_fonts(self.font, self.small_font)

        self.selected_item = None
        self.selected_type = None
        self.selected_student = None
        self.spawn_slider_rect = None  # Will be set in draw_ui
        self.dragging_spawn_slider = False

        # Debug and groups
        self.debug_paths = False
        self.group_id_counter = 0

        # Undo/redo system
        self.undo_history = []
        self.redo_history = []
        self.max_undo = 50

        self.load_layout()

    def hide_all_panels(self):
        self.station_panel.hide()
        self.table_panel.hide()
        self.dish_panel.hide()

    def select_item(self, item_type, item):
        self.selected_item = item
        self.selected_type = item_type
        self.hide_all_panels()
        if item_type == "station":
            self.station_panel.show(item)
        elif item_type == "table":
            self.table_panel.show(item)
        elif item_type == "dish_return":
            self.dish_panel.show(item)

    def load_background_image(self, path=None):
        if path is None:
            root = tk.Tk()
            root.withdraw()
            path = filedialog.askopenfilename(title="Select Image",
                filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.gif")])
            root.destroy()
        if path:
            try:
                self.background_image = pygame.transform.scale(
                    pygame.image.load(path), (self.play_area.width, self.play_area.height))
                self.background_path = path
            except Exception as e:
                print(f"Error: {e}")

    def load_layout(self):
        path = Path("config/layout.json")
        if not path.exists():
            return
        try:
            with open(path) as f:
                data = json.load(f)
            if data.get("background_image") and Path(data["background_image"]).exists():
                self.load_background_image(data["background_image"])
            for s in data.get("stations", []):
                self.stations.append(Station(
                    name=s["name"], x=s["x"], y=s["y"], width=s["width"], height=s["height"],
                    color=tuple(s["color"]), food_categories=set(s.get("food_categories", ["pizza"])),
                    popularity=s.get("popularity", 0.5), service_time=s.get("service_time", 6),
                    capacity=s.get("capacity", 1), queue_direction=s.get("queue_direction", "down"),
                    is_flow_through=s.get("is_flow_through", False),
                    flow_entry_side=s.get("flow_entry_side", "left"),
                    flow_exit_side=s.get("flow_exit_side", "right")
                ))
            for t in data.get("tables", []):
                self.tables.append(Table(x=t["x"], y=t["y"], seats=t.get("seats", 4), shape=t.get("shape", "circle")))
            for w in data.get("walls", []):
                self.walls.append(Wall(x1=w["x1"], y1=w["y1"], x2=w["x2"], y2=w["y2"]))
            for e in data.get("entrances", []):
                self.entrances.append(Entrance(x=e["x"], y=e["y"]))
            for e in data.get("exits", []):
                self.exits.append(Exit(x=e["x"], y=e["y"]))
            for d in data.get("dish_returns", []):
                self.dish_returns.append(DishReturn(x=d["x"], y=d["y"], width=d.get("width", 60),
                    height=d.get("height", 40), capacity=d.get("capacity", 1),
                    queue_direction=d.get("queue_direction", "down")))
            self.update_pathfinding()
            self.save_undo_state()  # Initial state for undo
        except Exception as e:
            print(f"Load error: {e}")

    def save_layout(self):
        data = {
            "background_image": self.background_path,
            "stations": [{
                "name": s.name, "x": s.x, "y": s.y, "width": s.width, "height": s.height,
                "color": list(s.color), "food_categories": list(s.food_categories),
                "popularity": s.popularity, "service_time": s.service_time, "capacity": s.capacity,
                "queue_direction": s.queue_direction, "is_flow_through": s.is_flow_through,
                "flow_entry_side": s.flow_entry_side, "flow_exit_side": s.flow_exit_side
            } for s in self.stations],
            "tables": [{"x": t.x, "y": t.y, "seats": t.seats, "shape": t.shape} for t in self.tables],
            "walls": [{"x1": w.x1, "y1": w.y1, "x2": w.x2, "y2": w.y2} for w in self.walls],
            "entrances": [{"x": e.x, "y": e.y} for e in self.entrances],
            "exits": [{"x": e.x, "y": e.y} for e in self.exits],
            "dish_returns": [{"x": d.x, "y": d.y, "width": d.width, "height": d.height,
                "capacity": d.capacity, "queue_direction": d.queue_direction} for d in self.dish_returns]
        }
        Path("config").mkdir(exist_ok=True)
        with open("config/layout.json", "w") as f:
            json.dump(data, f, indent=2)
        print("Saved!")

    def save_undo_state(self):
        """Save current layout state for undo"""
        state = {
            "stations": [(s.name, s.x, s.y, s.width, s.height, s.color, list(s.food_categories),
                         s.popularity, s.service_time, s.capacity, s.queue_direction,
                         s.is_flow_through, s.flow_entry_side, s.flow_exit_side) for s in self.stations],
            "tables": [(t.x, t.y, t.seats, t.shape) for t in self.tables],
            "walls": [(w.x1, w.y1, w.x2, w.y2) for w in self.walls],
            "entrances": [(e.x, e.y) for e in self.entrances],
            "exits": [(e.x, e.y) for e in self.exits],
            "dish_returns": [(d.x, d.y, d.width, d.height, d.capacity, d.queue_direction) for d in self.dish_returns],
        }
        self.undo_history.append(state)
        if len(self.undo_history) > self.max_undo:
            self.undo_history.pop(0)
        self.redo_history.clear()

    def restore_state(self, state):
        """Restore layout from saved state"""
        self.stations.clear()
        self.tables.clear()
        self.walls.clear()
        self.entrances.clear()
        self.exits.clear()
        self.dish_returns.clear()

        for s in state["stations"]:
            self.stations.append(Station(
                name=s[0], x=s[1], y=s[2], width=s[3], height=s[4], color=s[5],
                food_categories=set(s[6]), popularity=s[7], service_time=s[8],
                capacity=s[9], queue_direction=s[10], is_flow_through=s[11],
                flow_entry_side=s[12], flow_exit_side=s[13]
            ))
        for t in state["tables"]:
            self.tables.append(Table(x=t[0], y=t[1], seats=t[2], shape=t[3]))
        for w in state["walls"]:
            self.walls.append(Wall(x1=w[0], y1=w[1], x2=w[2], y2=w[3]))
        for e in state["entrances"]:
            self.entrances.append(Entrance(x=e[0], y=e[1]))
        for e in state["exits"]:
            self.exits.append(Exit(x=e[0], y=e[1]))
        for d in state["dish_returns"]:
            self.dish_returns.append(DishReturn(x=d[0], y=d[1], width=d[2], height=d[3], capacity=d[4], queue_direction=d[5]))

        self.selected_item = None
        self.hide_all_panels()
        self.update_pathfinding()

    def undo(self):
        """Undo last editor action"""
        if len(self.undo_history) < 2:
            return
        # Save current state to redo
        current = self.undo_history.pop()
        self.redo_history.append(current)
        # Restore previous state
        self.restore_state(self.undo_history[-1])

    def redo(self):
        """Redo last undone action"""
        if not self.redo_history:
            return
        state = self.redo_history.pop()
        self.undo_history.append(state)
        self.restore_state(state)

    def force_recalculate_paths(self):
        """Force all students to recalculate their paths"""
        for student in self.students:
            if student.state != StudentState.EXITED and student.target:
                student.path = self.pathfinder.find_path(student.pos, student.target)
                student.stuck_timer = 0

    def update_pathfinding(self):
        self.pathfinder.update_obstacles(self.walls, self.stations, self.tables)

    def spawn_student(self, entrance):
        # Determine if this is a group spawn
        is_group = random.random() < GROUP_CHANCE
        group_size = random.randint(GROUP_SIZE_MIN, GROUP_SIZE_MAX) if is_group else 1
        group_id = self.group_id_counter if is_group else -1

        if is_group:
            self.group_id_counter += 1

        # Pick a shared diet for group (groups of friends often eat similar)
        r = random.random()
        cumulative = 0
        base_diet = DietType.OMNIVORE
        for name, prob in DIET_DISTRIBUTION.items():
            cumulative += prob
            if r <= cumulative:
                base_diet = DietType[name.upper()]
                break

        for i in range(group_size):
            # Group members spawn near each other
            offset_x = random.randint(-12, 12) + (i % 2) * 10
            offset_y = random.randint(-12, 12) + (i // 2) * 10

            # Small chance group member has different diet
            diet = base_diet
            if is_group and random.random() < 0.15:
                r = random.random()
                cumulative = 0
                for name, prob in DIET_DISTRIBUTION.items():
                    cumulative += prob
                    if r <= cumulative:
                        diet = DietType[name.upper()]
                        break

            self.students.append(Student(
                id=self.student_id_counter,
                x=entrance.x + offset_x,
                y=entrance.y + offset_y,
                diet=diet,
                speed=random.uniform(STUDENT_SPEED * 0.85, STUDENT_SPEED * 1.15),
                group_id=group_id
            ))
            self.student_id_counter += 1

    def choose_station(self, student):
        compatible = [s for s in self.stations if s.can_serve_diet(student.diet) and not s.is_dessert_station()]
        if not compatible:
            return None
        scored = [(s.popularity * 100 - (len(s.queue) + len(s.being_served)) * 15 + random.randint(-15, 15), s)
                  for s in compatible]
        scored.sort(reverse=True, key=lambda x: x[0])
        return scored[0][1] if scored else None

    def choose_dessert_station(self, student):
        desserts = [s for s in self.stations if s.is_dessert_station()]
        if not desserts:
            return None
        return random.choice(desserts)

    def find_table(self, student=None):
        """Find a table, preferring one where group members are already seated"""
        available = [t for t in self.tables if t.has_space]
        if not available:
            return None

        # If student is in a group, try to find where group is seated
        if student and student.group_id >= 0:
            for table in available:
                for occupant in table.occupied_by:
                    if occupant.group_id == student.group_id:
                        return table

        return random.choice(available)

    def find_table_for_group(self, group_size: int):
        """Find a table with enough space for the whole group"""
        # Prefer tables that can fit the whole group
        perfect_fit = [t for t in self.tables if t.seats - len(t.occupied_by) >= group_size]
        if perfect_fit:
            return random.choice(perfect_fit)
        # Otherwise any table with space
        available = [t for t in self.tables if t.has_space]
        return random.choice(available) if available else None

    def get_group_members(self, group_id: int) -> List[Student]:
        """Get all students in a group"""
        if group_id < 0:
            return []
        return [s for s in self.students if s.group_id == group_id and s.state != StudentState.EXITED]

    def find_dish_return(self, pos):
        if not self.dish_returns:
            return None
        return min(self.dish_returns, key=lambda d: math.hypot(d.center[0] - pos[0], d.center[1] - pos[1]))

    def find_exit(self, pos):
        if not self.exits:
            return None
        return min(self.exits, key=lambda e: math.hypot(e.x - pos[0], e.y - pos[1]))

    def get_student_at(self, pos) -> Optional[Student]:
        for s in self.students:
            if s.state != StudentState.EXITED:
                if math.hypot(s.x - pos[0], s.y - pos[1]) < STUDENT_RADIUS + 5:
                    return s
        return None

    def apply_separation(self, student):
        """Apply separation forces to prevent overlapping"""
        for other in self.students:
            if other.id == student.id or other.state == StudentState.EXITED:
                continue
            # Skip separation for eating students at their seat
            if other.state == StudentState.EATING:
                continue

            dx = student.x - other.x
            dy = student.y - other.y
            dist = math.hypot(dx, dy)

            if 0.1 < dist < SEPARATION_RADIUS:
                # Stronger separation when very close
                force = ((SEPARATION_RADIUS - dist) / SEPARATION_RADIUS) ** 1.5
                if dist > 0:
                    student.vx += (dx / dist) * force * SEPARATION_FORCE
                    student.vy += (dy / dist) * force * SEPARATION_FORCE

    def apply_wall_avoidance(self, student):
        """Push students away from walls"""
        for wall in self.walls:
            rect = wall.get_rect()
            # Find closest point on wall
            cx = max(rect.left, min(student.x, rect.right))
            cy = max(rect.top, min(student.y, rect.bottom))

            dx = student.x - cx
            dy = student.y - cy
            dist = math.hypot(dx, dy)

            if 0 < dist < WALL_AVOIDANCE_RADIUS:
                force = ((WALL_AVOIDANCE_RADIUS - dist) / WALL_AVOIDANCE_RADIUS) ** 2
                student.vx += (dx / dist) * force * WALL_AVOIDANCE_FORCE
                student.vy += (dy / dist) * force * WALL_AVOIDANCE_FORCE

    def apply_table_avoidance(self, student):
        """Push students away from tables"""
        for table in self.tables:
            # Skip if student is seated at this table
            if student.target_table == table and student.state == StudentState.EATING:
                continue

            dx = student.x - table.x
            dy = student.y - table.y
            dist = math.hypot(dx, dy)
            avoid_dist = table.radius + TABLE_AVOIDANCE_RADIUS

            if 0 < dist < avoid_dist:
                force = ((avoid_dist - dist) / avoid_dist) ** 2
                student.vx += (dx / dist) * force * 1.0
                student.vy += (dy / dist) * force * 1.0

    def move_student(self, student, target) -> bool:
        """Move student toward target, returns True if reached"""
        # Reset velocity
        student.vx = 0
        student.vy = 0

        # Follow path if exists
        if student.path:
            next_pt = student.path[0]
            dx = next_pt[0] - student.x
            dy = next_pt[1] - student.y
            dist = math.hypot(dx, dy)

            if dist < student.speed * self.speed * 2.5:
                student.path.pop(0)
                if not student.path:
                    # Snap to target
                    student.x, student.y = target
                    return True
            else:
                # Move toward next path point
                student.vx = (dx / dist) * student.speed
                student.vy = (dy / dist) * student.speed
        else:
            # Direct movement
            dx = target[0] - student.x
            dy = target[1] - student.y
            dist = math.hypot(dx, dy)

            if dist < student.speed * self.speed * 2:
                student.x, student.y = target
                return True

            student.vx = (dx / dist) * student.speed
            student.vy = (dy / dist) * student.speed

        # Apply avoidance forces
        self.apply_separation(student)
        self.apply_wall_avoidance(student)
        self.apply_table_avoidance(student)

        # Calculate new position
        new_x = student.x + student.vx * self.speed
        new_y = student.y + student.vy * self.speed

        # Check wall collisions
        blocked = False
        for wall in self.walls:
            if wall.get_rect().inflate(STUDENT_RADIUS * 2, STUDENT_RADIUS * 2).collidepoint(new_x, new_y):
                blocked = True
                break

        # Check table collisions
        if not blocked:
            for table in self.tables:
                if student.target_table == table and student.state in [StudentState.EATING, StudentState.WALKING_TO_TABLE]:
                    continue
                if math.hypot(new_x - table.x, new_y - table.y) < table.radius + STUDENT_RADIUS:
                    blocked = True
                    break

        if not blocked:
            student.x = new_x
            student.y = new_y
            student.stuck_timer = 0
        else:
            student.stuck_timer += 1
            # Recalculate path if stuck
            if student.stuck_timer > 45 and target:
                student.path = self.pathfinder.find_path(student.pos, target)
                student.stuck_timer = 0

        # Keep in bounds
        student.x = max(STUDENT_RADIUS, min(self.play_area.width - STUDENT_RADIUS, student.x))
        student.y = max(STUDENT_RADIUS, min(WINDOW_HEIGHT - STUDENT_RADIUS, student.y))

        return False

    def update_station_queues(self):
        """Update queue positions for all stations"""
        for station in self.stations:
            if station.is_flow_through:
                continue

            # Assign queue positions to waiting students
            for i, student in enumerate(station.queue):
                student.queue_position = i + len(station.being_served)

            # Move front of queue to service if capacity allows
            while station.queue and len(station.being_served) < station.capacity:
                student = station.queue.pop(0)
                station.being_served.append(student)
                station.service_timers[student.id] = station.service_time * SERVICE_TIME_MULTIPLIER
                student.state = StudentState.BEING_SERVED
                student.queue_position = 0

    def update_dish_return_queues(self):
        """Update queue positions for dish returns"""
        for dr in self.dish_returns:
            # Assign queue positions
            for i, student in enumerate(dr.queue):
                student.queue_position = i + len(dr.being_served)

            # Move front to service
            while dr.queue and len(dr.being_served) < dr.capacity:
                student = dr.queue.pop(0)
                dr.being_served.append(student)
                student.eat_timer = DISH_RETURN_TIME
                student.state = StudentState.RETURNING_DISHES

    def update_student(self, student):
        student.time_in_system += 1

        if student.state == StudentState.ENTERING:
            station = self.choose_station(student)
            if station:
                student.target_station = station
                if station.is_flow_through:
                    student.target = station.get_flow_entry_point()
                else:
                    # Join end of queue
                    queue_pos = len(station.queue) + len(station.being_served)
                    student.target = station.get_queue_position(queue_pos)
                student.path = self.pathfinder.find_path(student.pos, student.target)
                student.state = StudentState.WALKING_TO_STATION
            elif self.exits:
                e = self.find_exit(student.pos)
                student.target = e.center
                student.path = self.pathfinder.find_path(student.pos, student.target)
                student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_STATION:
            station = student.target_station
            if station.is_flow_through:
                if self.move_student(student, student.target):
                    station.flow_positions.append(student)
                    student.flow_progress = 0
                    student.state = StudentState.IN_FLOW_ZONE
            else:
                # Get current queue end position
                queue_pos = len(station.queue) + len(station.being_served)
                queue_target = station.get_queue_position(queue_pos)

                # Count other students also walking to this station
                others_approaching = [s for s in self.students
                                     if s.id != student.id
                                     and s.state == StudentState.WALKING_TO_STATION
                                     and s.target_station == station]

                # Calculate distance to queue target
                dist_to_queue = math.hypot(student.x - queue_target[0], student.y - queue_target[1])

                # If far from queue, spread out approach
                if dist_to_queue > QUEUE_SPACING * 2:
                    # Find this student's index among approachers (use id for consistency)
                    approach_idx = sum(1 for s in others_approaching if s.id < student.id)

                    # Add perpendicular offset based on index
                    dx, dy = 0, 0
                    if station.queue_direction in ["up", "down"]:
                        dx = (approach_idx - len(others_approaching) / 2) * APPROACH_SPREAD
                    else:
                        dy = (approach_idx - len(others_approaching) / 2) * APPROACH_SPREAD

                    student.target = (queue_target[0] + dx, queue_target[1] + dy)
                else:
                    # Close enough - head directly to queue position
                    student.target = queue_target

                if self.move_student(student, student.target):
                    # Only join queue if actually at queue position
                    if dist_to_queue < QUEUE_SPACING:
                        station.queue.append(student)
                        student.state = StudentState.QUEUING
                        student.stations_visited.append(station.name)

        elif student.state == StudentState.IN_FLOW_ZONE:
            student.wait_time += 1
            station = student.target_station
            flow_path = station.get_flow_path(8)

            progress_rate = 1.0 / (station.service_time * SERVICE_TIME_MULTIPLIER / len(flow_path))
            student.flow_progress += progress_rate * self.speed

            if student.flow_progress >= len(flow_path) - 1:
                if student in station.flow_positions:
                    station.flow_positions.remove(student)
                student.has_food = True
                student.meals_eaten += 1
                student.stations_visited.append(station.name)
                table = self.find_table(student)
                if table:
                    student.target_table = table
                    table.occupied_by.append(student)
                    seats = table.get_seat_positions()
                    student.seat_position = seats[(len(table.occupied_by) - 1) % len(seats)]
                    student.target = student.seat_position
                    student.path = self.pathfinder.find_path(student.pos, student.target)
                    student.state = StudentState.WALKING_TO_TABLE
            else:
                idx = min(int(student.flow_progress), len(flow_path) - 1)
                self.move_student(student, flow_path[idx])

        elif student.state == StudentState.QUEUING:
            student.wait_time += 1
            station = student.target_station
            if student in station.queue:
                idx = station.queue.index(student) + len(station.being_served)
                target_pos = station.get_queue_position(idx)
                self.move_student(student, target_pos)

        elif student.state == StudentState.BEING_SERVED:
            station = student.target_station
            # Move to service point
            service_pt = station.get_service_point()
            self.move_student(student, service_pt)

            if student.id in station.service_timers:
                station.service_timers[student.id] -= self.speed
                if station.service_timers[student.id] <= 0:
                    if student in station.being_served:
                        station.being_served.remove(student)
                    del station.service_timers[student.id]
                    student.has_food = True
                    student.meals_eaten += 1

                    table = self.find_table(student)
                    if table:
                        student.target_table = table
                        table.occupied_by.append(student)
                        seats = table.get_seat_positions()
                        student.seat_position = seats[(len(table.occupied_by) - 1) % len(seats)]
                        student.target = student.seat_position
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_TABLE

        elif student.state == StudentState.WALKING_TO_TABLE:
            if self.move_student(student, student.target):
                student.eat_timer = random.randint(EAT_TIME_MIN, EAT_TIME_MAX)
                student.state = StudentState.EATING

        elif student.state == StudentState.EATING:
            student.eat_timer -= self.speed
            if student.seat_position:
                self.move_student(student, student.seat_position)

            if student.eat_timer <= 0:
                student.has_food = False
                if student.target_table and student in student.target_table.occupied_by:
                    student.target_table.occupied_by.remove(student)
                student.target_table = None

                # Decide what to do next
                r = random.random()
                if r < DESSERT_CHANCE and not student.has_dessert:
                    # Get dessert
                    dessert = self.choose_dessert_station(student)
                    if dessert:
                        student.target_station = dessert
                        queue_pos = len(dessert.queue) + len(dessert.being_served)
                        student.target = dessert.get_queue_position(queue_pos)
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_STATION
                        student.has_dessert = True
                        return

                # Go to dish return (unless has dessert - can leave with it)
                if student.has_dessert:
                    e = self.find_exit(student.pos)
                    if e:
                        student.target = e.center
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_EXIT
                else:
                    dr = self.find_dish_return(student.pos)
                    if dr:
                        student.target_dish_return = dr
                        queue_pos = len(dr.queue) + len(dr.being_served)
                        student.target = dr.get_queue_position(queue_pos)
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_DISH_RETURN
                    else:
                        e = self.find_exit(student.pos)
                        if e:
                            student.target = e.center
                            student.path = self.pathfinder.find_path(student.pos, student.target)
                            student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_DISH_RETURN:
            dr = student.target_dish_return
            if dr:
                # Update target to current queue position
                queue_pos = len(dr.queue) + len(dr.being_served)
                student.target = dr.get_queue_position(queue_pos)

                if self.move_student(student, student.target):
                    dr.queue.append(student)
                    student.state = StudentState.QUEUING_DISH_RETURN

        elif student.state == StudentState.QUEUING_DISH_RETURN:
            student.wait_time += 1
            dr = student.target_dish_return
            if dr and student in dr.queue:
                idx = dr.queue.index(student) + len(dr.being_served)
                target_pos = dr.get_queue_position(idx)
                self.move_student(student, target_pos)

        elif student.state == StudentState.RETURNING_DISHES:
            student.eat_timer -= self.speed
            dr = student.target_dish_return
            if dr:
                self.move_student(student, dr.center)

            if student.eat_timer <= 0:
                if dr and student in dr.being_served:
                    dr.being_served.remove(student)

                e = self.find_exit(student.pos)
                if e:
                    student.target = e.center
                    student.path = self.pathfinder.find_path(student.pos, student.target)
                    student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_EXIT:
            if self.move_student(student, student.target):
                student.state = StudentState.EXITED
                self.total_students_served += 1
                self.total_wait_time += student.wait_time
                self.total_time_in_system += student.time_in_system

    def update(self):
        if self.paused or self.editor_mode:
            return

        self.frame_count += 1

        # Spawn students
        spawn_interval = max(1, int(self.spawn_rate / self.speed))
        for entrance in self.entrances:
            if self.frame_count % spawn_interval == 0:
                self.spawn_student(entrance)

        # Update queue positions
        self.update_station_queues()
        self.update_dish_return_queues()

        # Update students
        for student in self.students:
            if student.state != StudentState.EXITED:
                self.update_student(student)

        # Remove old exited students
        exited = [s for s in self.students if s.state == StudentState.EXITED]
        if len(exited) > 50:
            for s in exited[:-50]:
                self.students.remove(s)

    def draw(self):
        if self.background_image:
            self.screen.blit(self.background_image, (0, 0))
        else:
            self.screen.fill(COLORS["background"])
            if self.editor_mode:
                for x in range(0, self.play_area.width, 50):
                    pygame.draw.line(self.screen, COLORS["grid"], (x, 0), (x, WINDOW_HEIGHT))
                for y in range(0, WINDOW_HEIGHT, 50):
                    pygame.draw.line(self.screen, COLORS["grid"], (0, y), (self.play_area.width, y))

        # Walls
        for wall in self.walls:
            pygame.draw.rect(self.screen, COLORS["wall"], wall.get_rect())

        # Entrances/Exits
        for ent in self.entrances:
            pygame.draw.circle(self.screen, COLORS["entrance"], ent.center, 16)
            pygame.draw.circle(self.screen, (255, 255, 255), ent.center, 16, 2)
            self.screen.blit(self.small_font.render("IN", True, COLORS["text_dark"]), (ent.x - 7, ent.y - 5))
        for ext in self.exits:
            pygame.draw.circle(self.screen, COLORS["exit"], ext.center, 16)
            pygame.draw.circle(self.screen, (255, 255, 255), ext.center, 16, 2)
            self.screen.blit(self.small_font.render("OUT", True, COLORS["text_dark"]), (ext.x - 10, ext.y - 5))

        # Dish returns
        for dr in self.dish_returns:
            rect = pygame.Rect(dr.x, dr.y, dr.width, dr.height)
            pygame.draw.rect(self.screen, COLORS["dish_return"], rect)
            pygame.draw.rect(self.screen, (255, 255, 255) if dr == self.selected_item else (200, 200, 200), rect, 2)
            self.screen.blit(self.small_font.render("DISHES", True, COLORS["text_dark"]), (dr.x + 2, dr.y + dr.height // 2 - 5))
            total_q = len(dr.queue) + len(dr.being_served)
            if total_q > 0:
                q_color = (255, 100, 100) if total_q > 3 else COLORS["text"]
                self.screen.blit(self.small_font.render(f"Q:{total_q}", True, q_color), (dr.x, dr.y + dr.height + 2))

        # Tables
        for table in self.tables:
            color = COLORS["table_occupied"] if table.occupied_by else COLORS["table"]
            if table.shape == "circle":
                pygame.draw.circle(self.screen, color, table.center, table.radius)
                pygame.draw.circle(self.screen, COLORS["selected"] if table == self.selected_item else (160, 160, 160),
                                  table.center, table.radius, 2)
            else:
                r = table.radius
                rect = pygame.Rect(table.x - r, table.y - r, r * 2, r * 2)
                pygame.draw.rect(self.screen, color, rect)
                pygame.draw.rect(self.screen, COLORS["selected"] if table == self.selected_item else (160, 160, 160), rect, 2)
            self.screen.blit(self.small_font.render(f"{len(table.occupied_by)}/{table.seats}", True, COLORS["text"]),
                            (table.x - 8, table.y - 5))

        # Stations
        for station in self.stations:
            rect = pygame.Rect(station.x, station.y, station.width, station.height)
            pygame.draw.rect(self.screen, station.color, rect)
            pygame.draw.rect(self.screen, COLORS["selected"] if station == self.selected_item else (255, 255, 255), rect, 2 if station != self.selected_item else 3)

            if station.is_flow_through:
                entry = station.get_flow_entry_point()
                exit_pt = station.get_flow_exit_point()
                pygame.draw.circle(self.screen, (100, 255, 100), entry, 6)
                pygame.draw.circle(self.screen, (255, 100, 100), exit_pt, 6)
                pygame.draw.line(self.screen, (150, 150, 200), entry, exit_pt, 2)

            self.screen.blit(self.small_font.render(station.name[:12], True, COLORS["text_dark"]), (station.x + 2, station.y + 2))
            q_len = len(station.queue) + len(station.being_served) + len(station.flow_positions)
            if q_len > 0:
                q_color = (255, 100, 100) if q_len > 5 else COLORS["text"]
                self.screen.blit(self.small_font.render(f"Q:{q_len}", True, q_color), (station.x, station.y + station.height + 2))

        # Students
        for student in self.students:
            if student.state != StudentState.EXITED:
                # Debug: draw path
                if self.debug_paths and student.path:
                    points = [(int(student.x), int(student.y))] + [(int(p[0]), int(p[1])) for p in student.path]
                    if len(points) > 1:
                        pygame.draw.lines(self.screen, (100, 200, 255), False, points, 1)
                        # Draw target marker
                        if student.target:
                            pygame.draw.circle(self.screen, (255, 100, 100), (int(student.target[0]), int(student.target[1])), 4, 1)

                # Group indicator ring
                if student.group_id >= 0:
                    pygame.draw.circle(self.screen, COLORS["group_ring"], (int(student.x), int(student.y)), STUDENT_RADIUS + 2, 1)

                # Highlight selected student
                if student == self.selected_student:
                    pygame.draw.circle(self.screen, COLORS["student_selected"], (int(student.x), int(student.y)), STUDENT_RADIUS + 3, 2)

                pygame.draw.circle(self.screen, student.color, (int(student.x), int(student.y)), STUDENT_RADIUS)
                if student.has_food:
                    pygame.draw.circle(self.screen, COLORS["student_has_food"], (int(student.x), int(student.y)), 2)

        # UI
        self.draw_ui()
        self.station_panel.draw(self.screen)
        self.table_panel.draw(self.screen)
        self.dish_panel.draw(self.screen)

        # Student info panel
        if self.selected_student and self.paused and not self.editor_mode:
            self.student_panel.draw(self.screen)

        pygame.display.flip()

    def draw_ui(self):
        active = len([s for s in self.students if s.state != StudentState.EXITED])
        avg_wait = (self.total_wait_time / max(1, self.total_students_served)) / 60

        # Calculate spawn rate display (higher spawn_rate = slower spawning)
        # Convert to a 1-10 scale where 10 is fastest
        spawn_display = int(10 - (self.spawn_rate - STUDENT_SPAWN_RATE_MIN) / (STUDENT_SPAWN_RATE_MAX - STUDENT_SPAWN_RATE_MIN) * 9)
        spawn_display = max(1, min(10, spawn_display))

        panel = pygame.Rect(5, 5, 210, 155)
        pygame.draw.rect(self.screen, COLORS["ui_bg"], panel)
        pygame.draw.rect(self.screen, (80, 80, 80), panel, 1)
        stats = [
            "[ EDITOR ]" if self.editor_mode else ("[ PAUSED ]" if self.paused else "[ RUNNING ]"),
            f"Active: {active} | Served: {self.total_students_served}",
            f"Avg Wait: {avg_wait:.1f}s | Speed: {self.speed:.1f}x",
        ]
        y = 8
        for s in stats:
            self.screen.blit(self.small_font.render(s, True, COLORS["text"]), (10, y))
            y += 15

        # Spawn rate slider
        y += 5
        self.screen.blit(self.small_font.render(f"Spawn Rate: {spawn_display}/10", True, COLORS["text"]), (10, y))
        y += 15
        slider_rect = pygame.Rect(10, y, 190, 12)
        pygame.draw.rect(self.screen, COLORS["slider_bg"], slider_rect, border_radius=3)
        fill_ratio = (STUDENT_SPAWN_RATE_MAX - self.spawn_rate) / (STUDENT_SPAWN_RATE_MAX - STUDENT_SPAWN_RATE_MIN)
        fill_width = int(fill_ratio * slider_rect.width)
        pygame.draw.rect(self.screen, COLORS["slider_fill"],
                        pygame.Rect(slider_rect.x, slider_rect.y, fill_width, slider_rect.height), border_radius=3)
        self.spawn_slider_rect = slider_rect  # Store for click handling

        y += 18
        self.screen.blit(self.small_font.render("SPACE=Run E=Edit R=Reset", True, COLORS["text"]), (10, y))
        y += 15
        self.screen.blit(self.small_font.render("D=Debug F=Recalc paths", True, COLORS["text"]), (10, y))
        y += 15
        if self.debug_paths:
            self.screen.blit(self.small_font.render("[DEBUG PATHS ON]", True, (100, 200, 255)), (10, y))
        elif self.paused and not self.editor_mode:
            self.screen.blit(self.small_font.render("Click student for stats", True, COLORS["text_muted"]), (10, y))

        if self.editor_mode:
            self.draw_toolbar()

    def draw_toolbar(self):
        y = WINDOW_HEIGHT - 50
        pygame.draw.rect(self.screen, COLORS["ui_bg"], (0, y, self.play_area.width, 50))
        pygame.draw.line(self.screen, (80, 80, 80), (0, y), (self.play_area.width, y))
        tools = [(EditorTool.SELECT, "0:Select"), (EditorTool.STATION, "1:Station"), (EditorTool.TABLE, "2:Table"),
                 (EditorTool.WALL, "3:Wall"), (EditorTool.ENTRANCE, "4:Enter"), (EditorTool.EXIT, "5:Exit"),
                 (EditorTool.DISH_RETURN, "6:Dishes")]
        x = 10
        for tool, label in tools:
            active = self.current_tool == tool
            rect = pygame.Rect(x, y + 8, 75, 34)
            pygame.draw.rect(self.screen, COLORS["button_active"] if active else COLORS["button"], rect, border_radius=4)
            pygame.draw.rect(self.screen, (120, 120, 120) if active else (80, 80, 80), rect, 1, border_radius=4)
            self.screen.blit(self.small_font.render(label, True, COLORS["text"]), (x + 6, y + 16))
            x += 82
        self.screen.blit(self.small_font.render("DEL=Delete C=Clear | Click items to edit", True, COLORS["text_muted"]), (x + 10, y + 18))

    def get_item_at(self, pos):
        x, y = pos
        for s in self.stations:
            if s.x <= x <= s.x + s.width and s.y <= y <= s.y + s.height:
                return ("station", s)
        for t in self.tables:
            if math.hypot(t.x - x, t.y - y) < t.radius + 5:
                return ("table", t)
        for w in self.walls:
            if w.get_rect().collidepoint(x, y):
                return ("wall", w)
        for e in self.entrances:
            if math.hypot(e.x - x, e.y - y) < 20:
                return ("entrance", e)
        for e in self.exits:
            if math.hypot(e.x - x, e.y - y) < 20:
                return ("exit", e)
        for d in self.dish_returns:
            if d.x <= x <= d.x + d.width and d.y <= y <= d.y + d.height:
                return ("dish_return", d)
        return (None, None)

    def handle_editor_click(self, pos, button):
        if button != 1:
            return
        if self.current_tool == EditorTool.SELECT:
            item_type, item = self.get_item_at(pos)
            if item:
                self.select_item(item_type, item)
            else:
                self.selected_item = None
                self.selected_type = None
                self.hide_all_panels()
        elif self.current_tool in [EditorTool.STATION, EditorTool.WALL, EditorTool.DISH_RETURN]:
            self.drawing = True
            self.draw_start = pos
        elif self.current_tool == EditorTool.TABLE:
            self.save_undo_state()
            t = Table(x=pos[0], y=pos[1], seats=4, shape="circle")
            self.tables.append(t)
            self.select_item("table", t)
            self.update_pathfinding()
        elif self.current_tool == EditorTool.ENTRANCE:
            self.save_undo_state()
            self.entrances.append(Entrance(x=pos[0], y=pos[1]))
        elif self.current_tool == EditorTool.EXIT:
            self.save_undo_state()
            self.exits.append(Exit(x=pos[0], y=pos[1]))

    def handle_editor_release(self, pos):
        if not self.drawing or not self.draw_start:
            return
        x, y = min(self.draw_start[0], pos[0]), min(self.draw_start[1], pos[1])
        w, h = abs(pos[0] - self.draw_start[0]), abs(pos[1] - self.draw_start[1])

        if self.current_tool == EditorTool.STATION and w > 20 and h > 20:
            self.save_undo_state()
            s = Station(name=f"Station {len(self.stations) + 1}", x=x, y=y, width=w, height=h,
                       color=(random.randint(150, 240), random.randint(150, 240), random.randint(100, 200)))
            self.stations.append(s)
            self.select_item("station", s)
            self.update_pathfinding()
        elif self.current_tool == EditorTool.WALL and (w > 5 or h > 5):
            self.save_undo_state()
            self.walls.append(Wall(x1=self.draw_start[0], y1=self.draw_start[1], x2=pos[0], y2=pos[1]))
            self.update_pathfinding()
        elif self.current_tool == EditorTool.DISH_RETURN and w > 20 and h > 20:
            self.save_undo_state()
            d = DishReturn(x=x, y=y, width=w, height=h)
            self.dish_returns.append(d)
            self.select_item("dish_return", d)

        self.drawing = False
        self.draw_start = None

    def delete_at(self, pos):
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
        if item == self.selected_item:
            self.selected_item = None
            self.hide_all_panels()
        self.update_pathfinding()

    def reset_simulation(self):
        self.students = []
        self.frame_count = 0
        self.total_students_served = self.total_wait_time = self.total_time_in_system = 0
        self.selected_student = None
        self.student_panel.hide()
        for s in self.stations:
            s.queue, s.being_served, s.service_timers, s.flow_positions = [], [], {}, []
        for t in self.tables:
            t.occupied_by = []
        for d in self.dish_returns:
            d.queue, d.being_served = [], []

    def clear_layout(self):
        self.save_undo_state()
        self.stations, self.tables, self.walls, self.entrances, self.exits, self.dish_returns = [], [], [], [], [], []
        self.selected_item = None
        self.hide_all_panels()
        self.reset_simulation()
        self.update_pathfinding()

    def run(self):
        print("=" * 50)
        print("DINING HALL FLOW SIMULATOR v2.5")
        print("Press L to load image, 0-6 for tools")
        print("D=debug paths, F=recalc routes")
        print("Ctrl+Z=undo, Ctrl+Y=redo")
        print("SPACE to run, click students for stats")
        print("=" * 50)

        while self.running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.running = False

                # Panels handle events first
                if self.station_panel.handle_event(event) or self.table_panel.handle_event(event) or self.dish_panel.handle_event(event):
                    continue

                if event.type == pygame.KEYDOWN:
                    if event.key in [pygame.K_ESCAPE, pygame.K_q]:
                        self.running = False
                    elif event.key == pygame.K_SPACE:
                        if self.editor_mode:
                            self.editor_mode = False
                            self.paused = False
                            self.hide_all_panels()
                            self.update_pathfinding()
                        else:
                            self.paused = not self.paused
                            if not self.paused:
                                self.selected_student = None
                                self.student_panel.hide()
                    elif event.key == pygame.K_e:
                        self.editor_mode = not self.editor_mode
                        if self.editor_mode:
                            self.paused = True
                            self.selected_student = None
                            self.student_panel.hide()
                    elif event.key == pygame.K_s:
                        self.save_layout()
                    elif event.key == pygame.K_l and self.editor_mode:
                        self.load_background_image()
                    elif event.key == pygame.K_c and self.editor_mode:
                        self.clear_layout()
                    elif event.key == pygame.K_r:
                        self.reset_simulation()
                    elif event.key in [pygame.K_PLUS, pygame.K_EQUALS]:
                        self.speed = min(10, self.speed + 0.5)
                    elif event.key == pygame.K_MINUS:
                        self.speed = max(0.5, self.speed - 0.5)
                    elif event.key == pygame.K_RIGHTBRACKET:  # ] = faster spawn
                        self.spawn_rate = max(STUDENT_SPAWN_RATE_MIN, self.spawn_rate - 20)
                    elif event.key == pygame.K_LEFTBRACKET:  # [ = slower spawn
                        self.spawn_rate = min(STUDENT_SPAWN_RATE_MAX, self.spawn_rate + 20)
                    elif event.key == pygame.K_d:  # D = toggle debug paths
                        self.debug_paths = not self.debug_paths
                    elif event.key == pygame.K_f:  # F = force recalculate paths
                        self.force_recalculate_paths()
                    elif event.key == pygame.K_z and pygame.key.get_mods() & pygame.KMOD_CTRL:
                        if self.editor_mode:
                            self.undo()
                    elif event.key == pygame.K_y and pygame.key.get_mods() & pygame.KMOD_CTRL:
                        if self.editor_mode:
                            self.redo()
                    elif event.key == pygame.K_DELETE and self.editor_mode:
                        self.save_undo_state()
                        self.delete_at(pygame.mouse.get_pos())
                    elif self.editor_mode:
                        tools = {pygame.K_0: EditorTool.SELECT, pygame.K_1: EditorTool.STATION, pygame.K_2: EditorTool.TABLE,
                                pygame.K_3: EditorTool.WALL, pygame.K_4: EditorTool.ENTRANCE, pygame.K_5: EditorTool.EXIT,
                                pygame.K_6: EditorTool.DISH_RETURN}
                        if event.key in tools:
                            self.current_tool = tools[event.key]

                elif event.type == pygame.MOUSEBUTTONDOWN:
                    # Check spawn rate slider click
                    if self.spawn_slider_rect and self.spawn_slider_rect.collidepoint(event.pos):
                        self.dragging_spawn_slider = True
                        ratio = (event.pos[0] - self.spawn_slider_rect.x) / self.spawn_slider_rect.width
                        ratio = max(0, min(1, ratio))
                        self.spawn_rate = int(STUDENT_SPAWN_RATE_MAX - ratio * (STUDENT_SPAWN_RATE_MAX - STUDENT_SPAWN_RATE_MIN))
                    elif self.editor_mode:
                        if event.pos[1] < WINDOW_HEIGHT - 50 and event.pos[0] < self.play_area.width:
                            self.handle_editor_click(event.pos, event.button)
                    elif self.paused and event.pos[0] < self.play_area.width:
                        # Click on student when paused
                        student = self.get_student_at(event.pos)
                        if student:
                            self.selected_student = student
                            self.student_panel.show(student)
                        else:
                            self.selected_student = None
                            self.student_panel.hide()

                elif event.type == pygame.MOUSEBUTTONUP:
                    self.dragging_spawn_slider = False
                    if self.editor_mode:
                        self.handle_editor_release(event.pos)

                elif event.type == pygame.MOUSEMOTION:
                    if self.dragging_spawn_slider and self.spawn_slider_rect:
                        ratio = (event.pos[0] - self.spawn_slider_rect.x) / self.spawn_slider_rect.width
                        ratio = max(0, min(1, ratio))
                        self.spawn_rate = int(STUDENT_SPAWN_RATE_MAX - ratio * (STUDENT_SPAWN_RATE_MAX - STUDENT_SPAWN_RATE_MIN))

            self.update()
            self.draw()

            if self.editor_mode and self.drawing and self.draw_start:
                mouse = pygame.mouse.get_pos()
                x, y = min(self.draw_start[0], mouse[0]), min(self.draw_start[1], mouse[1])
                w, h = abs(mouse[0] - self.draw_start[0]), abs(mouse[1] - self.draw_start[1])
                pygame.draw.rect(self.screen, (255, 255, 100), (x, y, w, h), 2)
                pygame.display.flip()

            self.clock.tick(60)
        pygame.quit()


if __name__ == "__main__":
    try:
        sim = DiningHallSimulation()
        sim.run()
    except Exception as e:
        print("=" * 50)
        print("CRASH ERROR:")
        print("=" * 50)
        traceback.print_exc()
        print("=" * 50)
        input("Press Enter to exit...")
    except KeyboardInterrupt:
        print("\nExiting...")
    finally:
        try:
            pygame.quit()
        except:
            pass
