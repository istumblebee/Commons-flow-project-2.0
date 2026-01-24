"""
Dining Hall Flow Simulator
===========================
A RollerCoaster Tycoon-style agent simulation for analyzing dining hall bottlenecks.

Controls:
    SPACE     - Pause/Resume simulation
    E         - Toggle Editor mode (place stations)
    +/-       - Speed up/slow down simulation
    S         - Save station layout
    R         - Reset simulation
    Q/ESC     - Quit

In Editor Mode:
    Left Click + Drag  - Draw a new station
    Right Click        - Delete station under cursor
    T                  - Place a table
    D                  - Place dish return
"""

import pygame
import json
import random
import math
from pathlib import Path
from enum import Enum
from dataclasses import dataclass, field
from typing import Optional

# ============================================================================
# CONFIGURATION - Edit these to customize your simulation!
# ============================================================================

# Window settings
WINDOW_WIDTH = 900
WINDOW_HEIGHT = 600

# Path to your dining hall image (put your image in the assets folder)
BACKGROUND_IMAGE = "assets/dining_hall.png"  # Change this to your image!

# How often students arrive (lower = more students)
STUDENT_SPAWN_RATE = 60  # frames between spawns (60 = ~1 per second at 60fps)

# Student dietary preferences distribution (should sum to 1.0)
DIET_DISTRIBUTION = {
    "omnivore": 0.60,      # Eats anything
    "vegetarian": 0.25,    # No meat
    "vegan": 0.15          # Plant-based only
}

# How long students eat (in simulation seconds)
EAT_TIME_MIN = 10 * 60   # 10 minutes in frames (at 60fps)
EAT_TIME_MAX = 20 * 60   # 20 minutes in frames

# Chance a student goes for seconds or dessert after eating
SECONDS_CHANCE = 0.25
DESSERT_CHANCE = 0.30

# Colors
COLORS = {
    "background": (40, 40, 45),
    "student": (255, 255, 100),
    "student_vegan": (100, 255, 100),
    "student_vegetarian": (150, 255, 150),
    "table": (139, 90, 43),
    "table_occupied": (100, 60, 30),
    "dish_return": (100, 100, 120),
    "entrance": (100, 200, 100),
    "exit": (200, 100, 100),
    "queue_line": (255, 255, 255, 50),
    "text": (255, 255, 255),
    "text_dark": (0, 0, 0),
}


# ============================================================================
# ENUMS AND DATA CLASSES
# ============================================================================

class StudentState(Enum):
    """What the student is currently doing"""
    ENTERING = "entering"
    BROWSING = "browsing"           # Looking around at options
    WALKING_TO_STATION = "walking_to_station"
    QUEUING = "queuing"             # Waiting in line
    BEING_SERVED = "being_served"
    WALKING_TO_TABLE = "walking_to_table"
    EATING = "eating"
    WALKING_TO_DISH_RETURN = "walking_to_dish_return"
    RETURNING_DISHES = "returning_dishes"
    WALKING_TO_EXIT = "walking_to_exit"
    GETTING_SECONDS = "getting_seconds"
    EXITED = "exited"


class DietType(Enum):
    """Dietary preferences"""
    OMNIVORE = "omnivore"
    VEGETARIAN = "vegetarian"
    VEGAN = "vegan"


@dataclass
class Station:
    """A food station in the dining hall"""
    name: str
    x: int
    y: int
    width: int
    height: int
    color: tuple
    food_type: str      # "meat", "vegetarian", "vegan", "all", "dessert"
    service_time: int   # seconds to serve one student
    capacity: int       # how many can be served at once
    queue: list = field(default_factory=list)
    being_served: list = field(default_factory=list)
    service_timers: dict = field(default_factory=dict)

    @property
    def center(self):
        return (self.x + self.width // 2, self.y + self.height // 2)

    @property
    def queue_position(self):
        """Where students line up"""
        return (self.x + self.width // 2, self.y + self.height + 20)

    def can_eat_here(self, diet: DietType) -> bool:
        """Check if student with this diet can eat at this station"""
        if self.food_type == "all":
            return True
        if self.food_type == "dessert":
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
    """A dining table"""
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


@dataclass
class Student:
    """An individual student agent"""
    id: int
    x: float
    y: float
    diet: DietType
    state: StudentState = StudentState.ENTERING
    target: tuple = None
    target_station: Station = None
    target_table: Table = None
    speed: float = 2.0
    eat_timer: int = 0
    has_food: bool = False
    meals_eaten: int = 0
    wants_dessert: bool = False
    is_browser: bool = False  # True if they look around first
    time_in_system: int = 0   # Track how long they've been here
    wait_time: int = 0        # Track time spent waiting in queues

    @property
    def color(self):
        if self.diet == DietType.VEGAN:
            return COLORS["student_vegan"]
        elif self.diet == DietType.VEGETARIAN:
            return COLORS["student_vegetarian"]
        return COLORS["student"]


# ============================================================================
# MAIN SIMULATION CLASS
# ============================================================================

class DiningHallSimulation:
    def __init__(self):
        pygame.init()
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        pygame.display.set_caption("Dining Hall Flow Simulator")
        self.clock = pygame.time.Clock()
        self.font = pygame.font.Font(None, 24)
        self.small_font = pygame.font.Font(None, 18)

        # Simulation state
        self.running = True
        self.paused = False
        self.speed = 1.0
        self.frame_count = 0
        self.student_id_counter = 0

        # Mode
        self.editor_mode = False
        self.drawing_station = False
        self.draw_start = None

        # Load or create layout
        self.stations = []
        self.tables = []
        self.dish_return = None
        self.entrance = (50, WINDOW_HEIGHT // 2)
        self.exit = (WINDOW_WIDTH - 50, WINDOW_HEIGHT // 2)

        # Active students
        self.students = []

        # Stats
        self.total_students_served = 0
        self.total_wait_time = 0
        self.total_time_in_system = 0

        # Load background image if exists
        self.background = None
        self.load_background()

        # Load station layout
        self.load_layout()

    def load_background(self):
        """Load the dining hall background image"""
        path = Path(BACKGROUND_IMAGE)
        if path.exists():
            try:
                self.background = pygame.image.load(str(path))
                self.background = pygame.transform.scale(
                    self.background,
                    (WINDOW_WIDTH, WINDOW_HEIGHT)
                )
                print(f"Loaded background: {path}")
            except Exception as e:
                print(f"Could not load background: {e}")
                self.background = None
        else:
            print(f"No background image found at {path}")
            print("Place your dining hall image there and restart!")

    def load_layout(self):
        """Load station layout from config file"""
        config_path = Path("config/stations.json")
        if config_path.exists():
            try:
                with open(config_path) as f:
                    data = json.load(f)

                # Load stations
                for s in data.get("stations", []):
                    station = Station(
                        name=s["name"],
                        x=s["x"],
                        y=s["y"],
                        width=s["width"],
                        height=s["height"],
                        color=tuple(s["color"]),
                        food_type=s["food_type"],
                        service_time=s["service_time"],
                        capacity=s["capacity"]
                    )
                    self.stations.append(station)

                # Load tables
                for t in data.get("tables", []):
                    table = Table(x=t["x"], y=t["y"], seats=t["seats"])
                    self.tables.append(table)

                # Load dish return
                dr = data.get("dish_return")
                if dr:
                    self.dish_return = (dr["x"], dr["y"], dr["width"], dr["height"])

                # Load entrance/exit
                ent = data.get("entrance")
                if ent:
                    self.entrance = (ent["x"], ent["y"])
                ext = data.get("exit")
                if ext:
                    self.exit = (ext["x"], ext["y"])

                print(f"Loaded {len(self.stations)} stations, {len(self.tables)} tables")
            except Exception as e:
                print(f"Error loading layout: {e}")
                self.create_default_layout()
        else:
            self.create_default_layout()

    def create_default_layout(self):
        """Create a basic default layout"""
        print("Creating default layout...")
        self.stations = [
            Station("Grill", 150, 100, 80, 60, (255, 100, 100), "meat", 8, 3),
            Station("Salad Bar", 300, 100, 100, 60, (100, 255, 100), "vegan", 5, 4),
            Station("Pizza", 450, 100, 80, 60, (255, 200, 100), "vegetarian", 6, 3),
        ]
        self.tables = [
            Table(200, 350, 4), Table(300, 350, 4), Table(400, 350, 4),
            Table(200, 450, 4), Table(300, 450, 4), Table(400, 450, 4),
        ]
        self.dish_return = (100, 500, 60, 40)

    def save_layout(self):
        """Save current layout to config file"""
        data = {
            "stations": [
                {
                    "name": s.name,
                    "x": s.x,
                    "y": s.y,
                    "width": s.width,
                    "height": s.height,
                    "color": list(s.color),
                    "food_type": s.food_type,
                    "service_time": s.service_time,
                    "capacity": s.capacity
                }
                for s in self.stations
            ],
            "tables": [
                {"x": t.x, "y": t.y, "seats": t.seats}
                for t in self.tables
            ],
            "dish_return": {
                "x": self.dish_return[0],
                "y": self.dish_return[1],
                "width": self.dish_return[2],
                "height": self.dish_return[3]
            } if self.dish_return else None,
            "entrance": {"x": self.entrance[0], "y": self.entrance[1]},
            "exit": {"x": self.exit[0], "y": self.exit[1]}
        }

        with open("config/stations.json", "w") as f:
            json.dump(data, f, indent=4)
        print("Layout saved!")

    def spawn_student(self):
        """Create a new student at the entrance"""
        # Determine diet based on distribution
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
            x=self.entrance[0],
            y=self.entrance[1] + random.randint(-20, 20),
            diet=diet,
            is_browser=random.random() < 0.3,  # 30% browse first
            speed=random.uniform(1.5, 2.5)
        )
        self.student_id_counter += 1
        self.students.append(student)

    def get_compatible_stations(self, student: Student) -> list:
        """Get stations where student can eat based on diet"""
        stations = [s for s in self.stations
                   if s.can_eat_here(student.diet) and s.food_type != "dessert"]
        return stations

    def get_dessert_station(self) -> Optional[Station]:
        """Get the dessert station if any"""
        for s in self.stations:
            if s.food_type == "dessert":
                return s
        return None

    def find_available_table(self) -> Optional[Table]:
        """Find a table with available seats"""
        available = [t for t in self.tables if t.has_space]
        if available:
            return random.choice(available)
        return None

    def move_toward(self, student: Student, target: tuple) -> bool:
        """Move student toward target, return True if arrived"""
        dx = target[0] - student.x
        dy = target[1] - student.y
        distance = math.sqrt(dx*dx + dy*dy)

        if distance < student.speed:
            student.x, student.y = target
            return True

        # Normalize and move
        student.x += (dx / distance) * student.speed * self.speed
        student.y += (dy / distance) * student.speed * self.speed
        return False

    def choose_station(self, student: Student) -> Optional[Station]:
        """AI: Choose which station to visit"""
        compatible = self.get_compatible_stations(student)
        if not compatible:
            return None

        # Simple AI: prefer shorter queues, but add some randomness
        scored = []
        for station in compatible:
            queue_penalty = len(station.queue) * 10
            random_factor = random.randint(0, 20)
            score = 100 - queue_penalty + random_factor
            scored.append((score, station))

        scored.sort(reverse=True, key=lambda x: x[0])
        return scored[0][1]

    def update_student(self, student: Student):
        """Update a single student's state and position"""
        student.time_in_system += 1

        if student.state == StudentState.ENTERING:
            # Just entered, decide what to do
            if student.is_browser:
                student.state = StudentState.BROWSING
                # Pick a random point in the middle to "browse"
                student.target = (
                    random.randint(200, WINDOW_WIDTH - 200),
                    random.randint(200, 300)
                )
            else:
                # Go directly to a station
                station = self.choose_station(student)
                if station:
                    student.target_station = station
                    student.target = station.queue_position
                    student.state = StudentState.WALKING_TO_STATION

        elif student.state == StudentState.BROWSING:
            # Walking around looking at options
            if self.move_toward(student, student.target):
                # Done browsing, pick a station
                station = self.choose_station(student)
                if station:
                    student.target_station = station
                    student.target = station.queue_position
                    student.state = StudentState.WALKING_TO_STATION

        elif student.state == StudentState.WALKING_TO_STATION:
            if self.move_toward(student, student.target):
                # Arrived at station, join queue
                student.target_station.queue.append(student)
                student.state = StudentState.QUEUING

        elif student.state == StudentState.QUEUING:
            student.wait_time += 1
            station = student.target_station

            # Update position in queue (visual)
            if student in station.queue:
                idx = station.queue.index(student)
                queue_x = station.queue_position[0]
                queue_y = station.queue_position[1] + idx * 15
                student.x = queue_x
                student.y = queue_y

            # Check if we can be served
            if (student in station.queue[:station.capacity] and
                len(station.being_served) < station.capacity):
                station.queue.remove(student)
                station.being_served.append(student)
                station.service_timers[student.id] = station.service_time * 60  # Convert to frames
                student.state = StudentState.BEING_SERVED

        elif student.state == StudentState.BEING_SERVED:
            station = student.target_station
            # Countdown service time
            station.service_timers[student.id] -= self.speed

            # Move to station position while being served
            self.move_toward(student, station.center)

            if station.service_timers[student.id] <= 0:
                # Done being served!
                station.being_served.remove(student)
                del station.service_timers[student.id]
                student.has_food = True
                student.meals_eaten += 1

                # Find a table
                table = self.find_available_table()
                if table:
                    student.target_table = table
                    table.occupied_by.append(student)
                    student.target = table.center
                    student.state = StudentState.WALKING_TO_TABLE
                else:
                    # No tables! Go straight to dish return (or wait?)
                    student.target = (self.dish_return[0], self.dish_return[1])
                    student.state = StudentState.WALKING_TO_DISH_RETURN

        elif student.state == StudentState.WALKING_TO_TABLE:
            if self.move_toward(student, student.target):
                # Arrived at table, start eating
                student.eat_timer = random.randint(EAT_TIME_MIN, EAT_TIME_MAX)
                student.state = StudentState.EATING

        elif student.state == StudentState.EATING:
            student.eat_timer -= self.speed
            if student.eat_timer <= 0:
                # Done eating!
                student.has_food = False
                if student.target_table:
                    if student in student.target_table.occupied_by:
                        student.target_table.occupied_by.remove(student)

                # Decide: exit, seconds, or dessert?
                if student.meals_eaten == 1:
                    if random.random() < DESSERT_CHANCE:
                        dessert = self.get_dessert_station()
                        if dessert:
                            student.wants_dessert = True
                            student.target_station = dessert
                            student.target = dessert.queue_position
                            student.state = StudentState.WALKING_TO_STATION
                        else:
                            student.target = (self.dish_return[0], self.dish_return[1])
                            student.state = StudentState.WALKING_TO_DISH_RETURN
                    elif random.random() < SECONDS_CHANCE:
                        # Get seconds from another station
                        station = self.choose_station(student)
                        if station:
                            student.target_station = station
                            student.target = station.queue_position
                            student.state = StudentState.WALKING_TO_STATION
                        else:
                            student.target = (self.dish_return[0], self.dish_return[1])
                            student.state = StudentState.WALKING_TO_DISH_RETURN
                    else:
                        student.target = (self.dish_return[0], self.dish_return[1])
                        student.state = StudentState.WALKING_TO_DISH_RETURN
                else:
                    # Already had seconds, leave
                    student.target = (self.dish_return[0], self.dish_return[1])
                    student.state = StudentState.WALKING_TO_DISH_RETURN

        elif student.state == StudentState.WALKING_TO_DISH_RETURN:
            if self.move_toward(student, student.target):
                student.state = StudentState.RETURNING_DISHES
                student.eat_timer = 60  # Brief pause at dish return

        elif student.state == StudentState.RETURNING_DISHES:
            student.eat_timer -= self.speed
            if student.eat_timer <= 0:
                student.target = self.exit
                student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_EXIT:
            if self.move_toward(student, student.target):
                student.state = StudentState.EXITED
                self.total_students_served += 1
                self.total_wait_time += student.wait_time
                self.total_time_in_system += student.time_in_system

    def update(self):
        """Main update loop"""
        if self.paused:
            return

        self.frame_count += 1

        # Spawn new students
        if self.frame_count % max(1, int(STUDENT_SPAWN_RATE / self.speed)) == 0:
            self.spawn_student()

        # Update all students
        for student in self.students:
            if student.state != StudentState.EXITED:
                self.update_student(student)

        # Remove exited students (keep last 100 for stats)
        exited = [s for s in self.students if s.state == StudentState.EXITED]
        if len(exited) > 100:
            for s in exited[:-100]:
                self.students.remove(s)

    def draw(self):
        """Render everything"""
        # Background
        if self.background:
            self.screen.blit(self.background, (0, 0))
        else:
            self.screen.fill(COLORS["background"])

        # Draw entrance/exit
        pygame.draw.circle(self.screen, COLORS["entrance"], self.entrance, 15)
        pygame.draw.circle(self.screen, COLORS["exit"], self.exit, 15)

        # Draw dish return
        if self.dish_return:
            pygame.draw.rect(self.screen, COLORS["dish_return"],
                           pygame.Rect(self.dish_return))
            text = self.small_font.render("Dish Return", True, COLORS["text"])
            self.screen.blit(text, (self.dish_return[0], self.dish_return[1] - 15))

        # Draw tables
        for table in self.tables:
            color = COLORS["table_occupied"] if table.occupied_by else COLORS["table"]
            pygame.draw.circle(self.screen, color, table.center, 20)
            # Draw seats
            text = self.small_font.render(
                f"{len(table.occupied_by)}/{table.seats}",
                True, COLORS["text"]
            )
            self.screen.blit(text, (table.x - 10, table.y - 8))

        # Draw stations
        for station in self.stations:
            # Station box
            pygame.draw.rect(self.screen, station.color,
                           pygame.Rect(station.x, station.y,
                                      station.width, station.height))
            pygame.draw.rect(self.screen, COLORS["text"],
                           pygame.Rect(station.x, station.y,
                                      station.width, station.height), 2)

            # Station name
            text = self.small_font.render(station.name, True, COLORS["text_dark"])
            self.screen.blit(text, (station.x + 5, station.y + 5))

            # Queue length
            queue_text = f"Queue: {len(station.queue)}"
            text = self.small_font.render(queue_text, True, COLORS["text"])
            self.screen.blit(text, (station.x, station.y + station.height + 5))

        # Draw students
        for student in self.students:
            if student.state != StudentState.EXITED:
                pygame.draw.circle(self.screen, student.color,
                                 (int(student.x), int(student.y)), 6)
                # Draw food indicator
                if student.has_food:
                    pygame.draw.circle(self.screen, (200, 150, 100),
                                     (int(student.x), int(student.y)), 3)

        # Draw UI
        self.draw_ui()

        # Draw editor overlay if in editor mode
        if self.editor_mode:
            self.draw_editor_ui()

        pygame.display.flip()

    def draw_ui(self):
        """Draw the UI overlay"""
        # Stats panel
        active_students = len([s for s in self.students
                              if s.state != StudentState.EXITED])

        # Calculate average times
        avg_wait = 0
        avg_time = 0
        if self.total_students_served > 0:
            avg_wait = (self.total_wait_time / self.total_students_served) / 60  # to seconds
            avg_time = (self.total_time_in_system / self.total_students_served) / 60

        stats = [
            f"Active Students: {active_students}",
            f"Total Served: {self.total_students_served}",
            f"Avg Wait Time: {avg_wait:.1f}s",
            f"Avg Total Time: {avg_time:.1f}s",
            f"Speed: {self.speed:.1f}x",
            "",
            "SPACE=Pause  E=Editor  +/-=Speed",
            "S=Save  R=Reset  Q=Quit"
        ]

        if self.paused:
            stats.insert(0, "=== PAUSED ===")

        y = 10
        for stat in stats:
            text = self.font.render(stat, True, COLORS["text"])
            # Draw background for readability
            pygame.draw.rect(self.screen, (0, 0, 0, 128),
                           (5, y - 2, text.get_width() + 10, 22))
            self.screen.blit(text, (10, y))
            y += 22

        # Show bottleneck warning
        for station in self.stations:
            if len(station.queue) > 5:
                warning = f"BOTTLENECK: {station.name} ({len(station.queue)} waiting)"
                text = self.font.render(warning, True, (255, 100, 100))
                pygame.draw.rect(self.screen, (50, 0, 0),
                               (WINDOW_WIDTH//2 - 150, 10, 300, 25))
                self.screen.blit(text, (WINDOW_WIDTH//2 - 140, 13))
                break

    def draw_editor_ui(self):
        """Draw editor mode overlay"""
        # Semi-transparent overlay
        overlay = pygame.Surface((WINDOW_WIDTH, 50))
        overlay.set_alpha(200)
        overlay.fill((50, 50, 80))
        self.screen.blit(overlay, (0, WINDOW_HEIGHT - 50))

        text = self.font.render(
            "EDITOR MODE | Click+Drag=New Station | T=Table | D=Dish Return | RightClick=Delete | S=Save",
            True, COLORS["text"]
        )
        self.screen.blit(text, (10, WINDOW_HEIGHT - 35))

        # Draw station being created
        if self.drawing_station and self.draw_start:
            mouse = pygame.mouse.get_pos()
            x = min(self.draw_start[0], mouse[0])
            y = min(self.draw_start[1], mouse[1])
            w = abs(mouse[0] - self.draw_start[0])
            h = abs(mouse[1] - self.draw_start[1])
            pygame.draw.rect(self.screen, (255, 255, 100),
                           pygame.Rect(x, y, w, h), 2)

    def handle_editor_click(self, pos, button):
        """Handle clicks in editor mode"""
        if button == 1:  # Left click
            if not self.drawing_station:
                self.drawing_station = True
                self.draw_start = pos
        elif button == 3:  # Right click - delete
            for station in self.stations[:]:
                if (station.x <= pos[0] <= station.x + station.width and
                    station.y <= pos[1] <= station.y + station.height):
                    self.stations.remove(station)
                    break
            for table in self.tables[:]:
                dist = math.sqrt((table.x - pos[0])**2 + (table.y - pos[1])**2)
                if dist < 25:
                    self.tables.remove(table)
                    break

    def handle_editor_release(self, pos):
        """Handle mouse release in editor mode"""
        if self.drawing_station and self.draw_start:
            x = min(self.draw_start[0], pos[0])
            y = min(self.draw_start[1], pos[1])
            w = abs(pos[0] - self.draw_start[0])
            h = abs(pos[1] - self.draw_start[1])

            if w > 20 and h > 20:  # Minimum size
                # Create new station with default values
                name = f"Station {len(self.stations) + 1}"
                color = (random.randint(100, 255),
                        random.randint(100, 255),
                        random.randint(100, 255))
                station = Station(
                    name=name,
                    x=x, y=y, width=w, height=h,
                    color=color,
                    food_type="all",
                    service_time=6,
                    capacity=3
                )
                self.stations.append(station)
                print(f"Created station: {name}")

        self.drawing_station = False
        self.draw_start = None

    def reset(self):
        """Reset the simulation"""
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
        print("Simulation reset!")

    def run(self):
        """Main game loop"""
        while self.running:
            # Handle events
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.running = False

                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE or event.key == pygame.K_q:
                        self.running = False
                    elif event.key == pygame.K_SPACE:
                        self.paused = not self.paused
                    elif event.key == pygame.K_e:
                        self.editor_mode = not self.editor_mode
                        if self.editor_mode:
                            self.paused = True
                    elif event.key == pygame.K_s:
                        self.save_layout()
                    elif event.key == pygame.K_r:
                        self.reset()
                    elif event.key == pygame.K_PLUS or event.key == pygame.K_EQUALS:
                        self.speed = min(10.0, self.speed + 0.5)
                    elif event.key == pygame.K_MINUS:
                        self.speed = max(0.5, self.speed - 0.5)
                    elif event.key == pygame.K_t and self.editor_mode:
                        pos = pygame.mouse.get_pos()
                        self.tables.append(Table(x=pos[0], y=pos[1], seats=4))
                        print(f"Added table at {pos}")
                    elif event.key == pygame.K_d and self.editor_mode:
                        pos = pygame.mouse.get_pos()
                        self.dish_return = (pos[0], pos[1], 60, 40)
                        print(f"Set dish return at {pos}")

                elif event.type == pygame.MOUSEBUTTONDOWN and self.editor_mode:
                    self.handle_editor_click(event.pos, event.button)

                elif event.type == pygame.MOUSEBUTTONUP and self.editor_mode:
                    self.handle_editor_release(event.pos)

            self.update()
            self.draw()
            self.clock.tick(60)

        pygame.quit()


# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("DINING HALL FLOW SIMULATOR")
    print("=" * 60)
    print()
    print("Controls:")
    print("  SPACE    - Pause/Resume")
    print("  E        - Toggle Editor mode")
    print("  +/-      - Speed up/slow down")
    print("  S        - Save layout")
    print("  R        - Reset simulation")
    print("  Q/ESC    - Quit")
    print()
    print("In Editor Mode:")
    print("  Click+Drag = Draw new station")
    print("  T          = Place table at cursor")
    print("  D          = Place dish return at cursor")
    print("  Right-Click= Delete item under cursor")
    print()
    print("TIP: Put your dining hall image at 'assets/dining_hall.png'")
    print("=" * 60)
    print()

    sim = DiningHallSimulation()
    sim.run()
