"""
Dining Hall Flow Simulator v2.1
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

    Click a station to open the properties panel
"""

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

# ============================================================================
# CONFIGURATION
# ============================================================================

WINDOW_WIDTH = 1400
WINDOW_HEIGHT = 900
PANEL_WIDTH = 280  # Right side panel width
GRID_SIZE = 8  # Smaller grid for better pathfinding

# Student settings
STUDENT_RADIUS = 5
STUDENT_SPAWN_RATE = 80
STUDENT_SPEED = 1.8
SEPARATION_RADIUS = 14
SEPARATION_FORCE = 0.6
WALL_AVOIDANCE_RADIUS = 15
WALL_AVOIDANCE_FORCE = 1.2

# Dietary distribution
DIET_DISTRIBUTION = {
    "omnivore": 0.55,
    "vegetarian": 0.25,
    "vegan": 0.12,
    "allergen_sensitive": 0.08
}

# Timing
EAT_TIME_MIN = 400
EAT_TIME_MAX = 900
DISH_RETURN_TIME = 45
SERVICE_TIME_MULTIPLIER = 60

SECONDS_CHANCE = 0.18
DESSERT_CHANCE = 0.22

# Colors
COLORS = {
    "background": (25, 25, 30),
    "grid": (35, 35, 40),
    "wall": (70, 70, 80),
    "student_omnivore": (255, 220, 100),
    "student_vegetarian": (150, 255, 150),
    "student_vegan": (100, 255, 100),
    "student_allergen": (255, 180, 220),
    "student_has_food": (180, 130, 80),
    "table": (120, 80, 40),
    "table_occupied": (90, 55, 25),
    "dish_return": (100, 100, 120),
    "entrance": (80, 180, 80),
    "exit": (180, 80, 80),
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
}

# Food categories
FOOD_CATEGORIES = [
    ("pizza", "Pizza", (255, 180, 100)),
    ("burgers", "Burgers/Grill", (200, 100, 80)),
    ("vegan", "Vegan", (100, 200, 100)),
    ("vegetarian", "Vegetarian", (150, 220, 150)),
    ("allergen_friendly", "Allergen Friendly", (200, 150, 255)),
    ("salad", "Salad Bar", (100, 180, 100)),
    ("asian", "Asian/Wok", (255, 150, 100)),
    ("deli", "Deli/Sandwich", (220, 180, 140)),
    ("soup", "Soup", (180, 140, 100)),
    ("dessert", "Dessert", (255, 180, 200)),
    ("beverage", "Beverages", (150, 200, 255)),
    ("breakfast", "Breakfast", (255, 220, 150)),
]


# ============================================================================
# ENUMS AND DATA CLASSES
# ============================================================================

class StudentState(Enum):
    ENTERING = "entering"
    WALKING_TO_STATION = "walking"
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


class EditorTool(Enum):
    SELECT = 0
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

    # Food offerings (which categories this station serves)
    food_categories: Set[str] = field(default_factory=lambda: {"pizza"})

    # Station properties
    popularity: float = 0.5  # 0-1, affects how often students choose this
    service_time: float = 6.0  # seconds per student
    capacity: int = 3  # how many can be served at once

    # Runtime state
    queue: list = field(default_factory=list)
    being_served: list = field(default_factory=list)
    service_timers: dict = field(default_factory=dict)
    queue_direction: str = "down"

    @property
    def center(self):
        return (self.x + self.width // 2, self.y + self.height // 2)

    @property
    def service_positions(self) -> List[Tuple[int, int]]:
        positions = []
        spacing = self.width // (self.capacity + 1)
        for i in range(self.capacity):
            px = self.x + spacing * (i + 1)
            py = self.y + self.height // 2
            positions.append((px, py))
        return positions

    def get_queue_positions(self, count: int) -> List[Tuple[int, int]]:
        positions = []
        spacing = SEPARATION_RADIUS + 3

        if self.queue_direction == "down":
            start_x = self.x + self.width // 2
            start_y = self.y + self.height + 12
            for i in range(count):
                positions.append((start_x, start_y + i * spacing))
        elif self.queue_direction == "up":
            start_x = self.x + self.width // 2
            start_y = self.y - 12
            for i in range(count):
                positions.append((start_x, start_y - i * spacing))
        elif self.queue_direction == "left":
            start_x = self.x - 12
            start_y = self.y + self.height // 2
            for i in range(count):
                positions.append((start_x - i * spacing, start_y))
        else:
            start_x = self.x + self.width + 12
            start_y = self.y + self.height // 2
            for i in range(count):
                positions.append((start_x + i * spacing, start_y))
        return positions

    def can_serve_diet(self, diet: DietType) -> bool:
        """Check if this station can serve a student with this diet"""
        if diet == DietType.VEGAN:
            return "vegan" in self.food_categories
        elif diet == DietType.VEGETARIAN:
            return any(cat in self.food_categories for cat in ["vegan", "vegetarian", "salad", "soup", "dessert", "beverage"])
        elif diet == DietType.ALLERGEN_SENSITIVE:
            return "allergen_friendly" in self.food_categories
        else:  # Omnivore
            return len(self.food_categories) > 0

    def is_dessert_station(self) -> bool:
        return "dessert" in self.food_categories and len(self.food_categories) == 1


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
        positions = []
        radius = 22
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
    thickness: int = 6

    def get_rect(self) -> pygame.Rect:
        x = min(self.x1, self.x2)
        y = min(self.y1, self.y2)
        w = max(abs(self.x2 - self.x1), self.thickness)
        h = max(abs(self.y2 - self.y1), self.thickness)
        return pygame.Rect(x, y, w, h)

    def get_expanded_rect(self, margin: int) -> pygame.Rect:
        rect = self.get_rect()
        return rect.inflate(margin * 2, margin * 2)


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
        spacing = SEPARATION_RADIUS + 3
        start_x = self.x + self.width // 2
        start_y = self.y + self.height + 12
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
    vx: float = 0
    vy: float = 0
    stuck_timer: int = 0  # Track if stuck

    @property
    def color(self):
        if self.diet == DietType.VEGAN:
            return COLORS["student_vegan"]
        elif self.diet == DietType.VEGETARIAN:
            return COLORS["student_vegetarian"]
        elif self.diet == DietType.ALLERGEN_SENSITIVE:
            return COLORS["student_allergen"]
        return COLORS["student_omnivore"]

    @property
    def pos(self):
        return (self.x, self.y)


# ============================================================================
# UI COMPONENTS
# ============================================================================

class Slider:
    def __init__(self, x, y, width, min_val, max_val, value, label, format_str="{:.1f}"):
        self.rect = pygame.Rect(x, y, width, 20)
        self.min_val = min_val
        self.max_val = max_val
        self.value = value
        self.label = label
        self.format_str = format_str
        self.dragging = False

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEBUTTONDOWN:
            if self.rect.collidepoint(event.pos):
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
        ratio = (mouse_x - self.rect.x) / self.rect.width
        ratio = max(0, min(1, ratio))
        self.value = self.min_val + ratio * (self.max_val - self.min_val)

    def draw(self, screen, font):
        # Label
        label_text = font.render(f"{self.label}: {self.format_str.format(self.value)}", True, COLORS["text"])
        screen.blit(label_text, (self.rect.x, self.rect.y - 18))

        # Background
        pygame.draw.rect(screen, COLORS["slider_bg"], self.rect, border_radius=3)

        # Fill
        fill_width = int((self.value - self.min_val) / (self.max_val - self.min_val) * self.rect.width)
        fill_rect = pygame.Rect(self.rect.x, self.rect.y, fill_width, self.rect.height)
        pygame.draw.rect(screen, COLORS["slider_fill"], fill_rect, border_radius=3)

        # Handle
        handle_x = self.rect.x + fill_width
        pygame.draw.circle(screen, COLORS["text"], (handle_x, self.rect.centery), 8)


class Checkbox:
    def __init__(self, x, y, label, checked=False, color=None):
        self.rect = pygame.Rect(x, y, 18, 18)
        self.label = label
        self.checked = checked
        self.color = color or COLORS["checkbox_check"]

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEBUTTONDOWN:
            # Check if click is on checkbox or label area
            click_area = pygame.Rect(self.rect.x, self.rect.y, 200, self.rect.height)
            if click_area.collidepoint(event.pos):
                self.checked = not self.checked
                return True
        return False

    def draw(self, screen, font):
        # Box
        pygame.draw.rect(screen, COLORS["input_bg"], self.rect)
        pygame.draw.rect(screen, COLORS["text_muted"], self.rect, 1)

        # Check mark
        if self.checked:
            inner = self.rect.inflate(-6, -6)
            pygame.draw.rect(screen, self.color, inner)

        # Label
        label_text = font.render(self.label, True, COLORS["text"])
        screen.blit(label_text, (self.rect.right + 8, self.rect.y + 1))


class TextInput:
    def __init__(self, x, y, width, value="", label=""):
        self.rect = pygame.Rect(x, y, width, 26)
        self.value = value
        self.label = label
        self.active = False
        self.cursor_visible = True
        self.cursor_timer = 0

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEBUTTONDOWN:
            self.active = self.rect.collidepoint(event.pos)
            return self.active
        elif event.type == pygame.KEYDOWN and self.active:
            if event.key == pygame.K_BACKSPACE:
                self.value = self.value[:-1]
            elif event.key == pygame.K_RETURN:
                self.active = False
            elif event.unicode.isprintable():
                self.value += event.unicode
            return True
        return False

    def draw(self, screen, font):
        # Label
        if self.label:
            label_text = font.render(self.label, True, COLORS["text"])
            screen.blit(label_text, (self.rect.x, self.rect.y - 18))

        # Background
        bg_color = COLORS["button_active"] if self.active else COLORS["input_bg"]
        pygame.draw.rect(screen, bg_color, self.rect, border_radius=3)
        pygame.draw.rect(screen, COLORS["text_muted"], self.rect, 1, border_radius=3)

        # Text
        text_surface = font.render(self.value, True, COLORS["text"])
        screen.blit(text_surface, (self.rect.x + 6, self.rect.y + 5))

        # Cursor
        if self.active:
            self.cursor_timer += 1
            if self.cursor_timer % 60 < 30:
                cursor_x = self.rect.x + 6 + text_surface.get_width()
                pygame.draw.line(screen, COLORS["text"],
                               (cursor_x, self.rect.y + 4),
                               (cursor_x, self.rect.y + 22))


class Button:
    def __init__(self, x, y, width, height, label, color=None):
        self.rect = pygame.Rect(x, y, width, height)
        self.label = label
        self.color = color or COLORS["button"]
        self.hovered = False

    def handle_event(self, event) -> bool:
        if event.type == pygame.MOUSEMOTION:
            self.hovered = self.rect.collidepoint(event.pos)
        elif event.type == pygame.MOUSEBUTTONDOWN:
            if self.rect.collidepoint(event.pos):
                return True
        return False

    def draw(self, screen, font):
        color = COLORS["button_hover"] if self.hovered else self.color
        pygame.draw.rect(screen, color, self.rect, border_radius=4)
        pygame.draw.rect(screen, COLORS["text_muted"], self.rect, 1, border_radius=4)

        text = font.render(self.label, True, COLORS["text"])
        text_rect = text.get_rect(center=self.rect.center)
        screen.blit(text, text_rect)


# ============================================================================
# PATHFINDING (Improved)
# ============================================================================

class Pathfinder:
    def __init__(self, width, height, grid_size):
        self.width = width
        self.height = height
        self.grid_size = grid_size
        self.cols = width // grid_size
        self.rows = height // grid_size
        self.obstacles = set()
        self.wall_adjacents = set()  # Cells next to walls for extra avoidance

    def update_obstacles(self, walls: List[Wall], stations: List[Station]):
        self.obstacles.clear()
        self.wall_adjacents.clear()

        margin = 2  # Extra cells around walls

        for wall in walls:
            rect = wall.get_rect()
            # Mark wall cells
            for gx in range(rect.left // self.grid_size - margin,
                          (rect.right // self.grid_size) + margin + 1):
                for gy in range(rect.top // self.grid_size - margin,
                              (rect.bottom // self.grid_size) + margin + 1):
                    if 0 <= gx < self.cols and 0 <= gy < self.rows:
                        # Core wall cells are obstacles
                        if (rect.left // self.grid_size <= gx <= rect.right // self.grid_size and
                            rect.top // self.grid_size <= gy <= rect.bottom // self.grid_size):
                            self.obstacles.add((gx, gy))
                        else:
                            # Adjacent cells have higher cost
                            self.wall_adjacents.add((gx, gy))

        for station in stations:
            for gx in range(station.x // self.grid_size,
                          (station.x + station.width) // self.grid_size + 1):
                for gy in range(station.y // self.grid_size,
                              (station.y + station.height) // self.grid_size + 1):
                    if 0 <= gx < self.cols and 0 <= gy < self.rows:
                        self.obstacles.add((gx, gy))

    def heuristic(self, a, b):
        return math.sqrt((a[0] - b[0])**2 + (a[1] - b[1])**2)

    def get_neighbors(self, pos):
        x, y = pos
        neighbors = []
        for dx, dy in [(0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)]:
            nx, ny = x + dx, y + dy
            if 0 <= nx < self.cols and 0 <= ny < self.rows:
                if (nx, ny) not in self.obstacles:
                    neighbors.append((nx, ny))
        return neighbors

    def find_path(self, start: Tuple[int, int], goal: Tuple[int, int]) -> List[Tuple[int, int]]:
        start_grid = (int(start[0] // self.grid_size), int(start[1] // self.grid_size))
        goal_grid = (int(goal[0] // self.grid_size), int(goal[1] // self.grid_size))

        start_grid = (max(0, min(start_grid[0], self.cols-1)),
                     max(0, min(start_grid[1], self.rows-1)))
        goal_grid = (max(0, min(goal_grid[0], self.cols-1)),
                    max(0, min(goal_grid[1], self.rows-1)))

        if start_grid in self.obstacles:
            start_grid = self._find_nearest_free(start_grid)
        if goal_grid in self.obstacles:
            goal_grid = self._find_nearest_free(goal_grid)

        if start_grid is None or goal_grid is None:
            return [goal]

        frontier = [(0, start_grid)]
        came_from = {start_grid: None}
        cost_so_far = {start_grid: 0}

        while frontier:
            _, current = heapq.heappop(frontier)

            if current == goal_grid:
                break

            for next_pos in self.get_neighbors(current):
                # Base movement cost
                is_diagonal = abs(next_pos[0] - current[0]) + abs(next_pos[1] - current[1]) == 2
                move_cost = 1.4 if is_diagonal else 1.0

                # Extra cost for cells near walls (encourages staying away from walls)
                if next_pos in self.wall_adjacents:
                    move_cost += 2.0

                new_cost = cost_so_far[current] + move_cost

                if next_pos not in cost_so_far or new_cost < cost_so_far[next_pos]:
                    cost_so_far[next_pos] = new_cost
                    priority = new_cost + self.heuristic(next_pos, goal_grid)
                    heapq.heappush(frontier, (priority, next_pos))
                    came_from[next_pos] = current

        if goal_grid not in came_from:
            return [goal]

        path = []
        current = goal_grid
        while current is not None:
            wx = current[0] * self.grid_size + self.grid_size // 2
            wy = current[1] * self.grid_size + self.grid_size // 2
            path.append((wx, wy))
            current = came_from[current]

        path.reverse()

        # Smooth path
        if len(path) > 2:
            smoothed = [path[0]]
            for i in range(1, len(path) - 1):
                prev = smoothed[-1]
                curr = path[i]
                next_p = path[i + 1]
                dx1, dy1 = curr[0] - prev[0], curr[1] - prev[1]
                dx2, dy2 = next_p[0] - curr[0], next_p[1] - curr[1]
                if (dx1, dy1) != (dx2, dy2):
                    smoothed.append(curr)
            smoothed.append(path[-1])
            path = smoothed

        path.append(goal)
        return path[1:] if len(path) > 1 else [goal]

    def _find_nearest_free(self, pos):
        for radius in range(1, 30):
            for dx in range(-radius, radius + 1):
                for dy in range(-radius, radius + 1):
                    check = (pos[0] + dx, pos[1] + dy)
                    if 0 <= check[0] < self.cols and 0 <= check[1] < self.rows:
                        if check not in self.obstacles:
                            return check
        return None


# ============================================================================
# STATION PROPERTIES PANEL
# ============================================================================

class StationPropertiesPanel:
    def __init__(self, x, y, width, height):
        self.rect = pygame.Rect(x, y, width, height)
        self.visible = False
        self.station: Optional[Station] = None
        self.scroll_offset = 0

        # UI elements (will be created when station is selected)
        self.name_input = None
        self.popularity_slider = None
        self.service_time_slider = None
        self.capacity_slider = None
        self.food_checkboxes = []
        self.queue_direction_buttons = []
        self.close_button = None

        self.font = None
        self.small_font = None

    def init_fonts(self, font, small_font):
        self.font = font
        self.small_font = small_font

    def show(self, station: Station):
        self.station = station
        self.visible = True
        self.scroll_offset = 0
        self._create_ui_elements()

    def hide(self):
        self.visible = False
        self.station = None

    def _create_ui_elements(self):
        if not self.station:
            return

        x = self.rect.x + 15
        y = self.rect.y + 50
        w = self.rect.width - 30

        # Name input
        self.name_input = TextInput(x, y, w, self.station.name, "Station Name")
        y += 55

        # Popularity slider
        self.popularity_slider = Slider(x, y, w, 0.0, 1.0, self.station.popularity,
                                        "Popularity", "{:.0%}")
        y += 50

        # Service time slider
        self.service_time_slider = Slider(x, y, w, 1.0, 20.0, self.station.service_time,
                                          "Service Time (sec)")
        y += 50

        # Capacity slider
        self.capacity_slider = Slider(x, y, w, 1, 8, self.station.capacity,
                                      "Capacity", "{:.0f}")
        y += 55

        # Queue direction buttons
        self.queue_direction_buttons = []
        btn_w = (w - 15) // 4
        directions = [("down", "↓"), ("up", "↑"), ("left", "←"), ("right", "→")]
        for i, (direction, symbol) in enumerate(directions):
            btn = Button(x + i * (btn_w + 5), y, btn_w, 28, symbol)
            btn.direction = direction
            self.queue_direction_buttons.append(btn)
        y += 45

        # Food category checkboxes
        self.food_checkboxes = []
        for cat_id, cat_name, cat_color in FOOD_CATEGORIES:
            checked = cat_id in self.station.food_categories
            cb = Checkbox(x, y, cat_name, checked, cat_color)
            cb.category_id = cat_id
            self.food_checkboxes.append(cb)
            y += 26

        y += 15

        # Close button
        self.close_button = Button(x, y, w, 32, "Close Panel")

    def handle_event(self, event) -> bool:
        if not self.visible:
            return False

        # Check if click is inside panel
        if event.type == pygame.MOUSEBUTTONDOWN:
            if not self.rect.collidepoint(event.pos):
                return False

        # Handle UI elements
        if self.name_input and self.name_input.handle_event(event):
            self.station.name = self.name_input.value
            return True

        if self.popularity_slider and self.popularity_slider.handle_event(event):
            self.station.popularity = self.popularity_slider.value
            return True

        if self.service_time_slider and self.service_time_slider.handle_event(event):
            self.station.service_time = self.service_time_slider.value
            return True

        if self.capacity_slider and self.capacity_slider.handle_event(event):
            self.station.capacity = int(self.capacity_slider.value)
            return True

        # Queue direction
        for btn in self.queue_direction_buttons:
            if btn.handle_event(event):
                self.station.queue_direction = btn.direction
                return True

        # Food checkboxes
        for cb in self.food_checkboxes:
            if cb.handle_event(event):
                if cb.checked:
                    self.station.food_categories.add(cb.category_id)
                else:
                    self.station.food_categories.discard(cb.category_id)
                return True

        # Close button
        if self.close_button and self.close_button.handle_event(event):
            self.hide()
            return True

        return self.rect.collidepoint(pygame.mouse.get_pos())

    def draw(self, screen):
        if not self.visible:
            return

        # Panel background
        pygame.draw.rect(screen, COLORS["panel_bg"], self.rect)
        pygame.draw.line(screen, COLORS["text_muted"],
                        (self.rect.x, self.rect.y),
                        (self.rect.x, self.rect.bottom))

        # Title
        title = self.font.render("Station Properties", True, COLORS["text"])
        screen.blit(title, (self.rect.x + 15, self.rect.y + 15))

        # Draw UI elements
        if self.name_input:
            self.name_input.draw(screen, self.small_font)
        if self.popularity_slider:
            self.popularity_slider.draw(screen, self.small_font)
        if self.service_time_slider:
            self.service_time_slider.draw(screen, self.small_font)
        if self.capacity_slider:
            self.capacity_slider.draw(screen, self.small_font)

        # Queue direction label
        if self.queue_direction_buttons:
            label = self.small_font.render("Queue Direction:", True, COLORS["text"])
            screen.blit(label, (self.queue_direction_buttons[0].rect.x,
                               self.queue_direction_buttons[0].rect.y - 18))
            for btn in self.queue_direction_buttons:
                # Highlight active direction
                if btn.direction == self.station.queue_direction:
                    btn.color = COLORS["button_active"]
                else:
                    btn.color = COLORS["button"]
                btn.draw(screen, self.small_font)

        # Food categories label
        if self.food_checkboxes:
            label = self.small_font.render("Food Categories:", True, COLORS["text"])
            screen.blit(label, (self.food_checkboxes[0].rect.x,
                               self.food_checkboxes[0].rect.y - 20))
            for cb in self.food_checkboxes:
                cb.draw(screen, self.small_font)

        if self.close_button:
            self.close_button.draw(screen, self.small_font)


# ============================================================================
# MAIN SIMULATION
# ============================================================================

class DiningHallSimulation:
    def __init__(self):
        pygame.init()
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        pygame.display.set_caption("Dining Hall Flow Simulator v2.1")
        self.clock = pygame.time.Clock()
        self.font = pygame.font.Font(None, 24)
        self.small_font = pygame.font.Font(None, 18)
        self.large_font = pygame.font.Font(None, 32)

        # Play area (excluding panel)
        self.play_area = pygame.Rect(0, 0, WINDOW_WIDTH - PANEL_WIDTH, WINDOW_HEIGHT)

        # Simulation state
        self.running = True
        self.paused = True
        self.speed = 1.0
        self.frame_count = 0
        self.student_id_counter = 0

        # Editor state
        self.editor_mode = True
        self.current_tool = EditorTool.SELECT
        self.drawing = False
        self.draw_start = None
        self.selected_station = None

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
        self.pathfinder = Pathfinder(self.play_area.width, WINDOW_HEIGHT, GRID_SIZE)

        # Background image
        self.background_image = None
        self.background_path = None

        # Stats
        self.total_students_served = 0
        self.total_wait_time = 0
        self.total_time_in_system = 0

        # Properties panel
        self.properties_panel = StationPropertiesPanel(
            WINDOW_WIDTH - PANEL_WIDTH, 0, PANEL_WIDTH, WINDOW_HEIGHT
        )
        self.properties_panel.init_fonts(self.font, self.small_font)

        # Load existing layout
        self.load_layout()

    def load_background_image(self, path: str = None):
        if path is None:
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
                    (self.play_area.width, self.play_area.height)
                )
                self.background_path = path
                print(f"Loaded background: {path}")
            except Exception as e:
                print(f"Error loading image: {e}")

    def load_layout(self):
        config_path = Path("config/layout.json")
        if not config_path.exists():
            return

        try:
            with open(config_path) as f:
                data = json.load(f)

            if data.get("background_image"):
                bg_path = Path(data["background_image"])
                if bg_path.exists():
                    self.load_background_image(str(bg_path))

            for s in data.get("stations", []):
                station = Station(
                    name=s["name"],
                    x=s["x"], y=s["y"],
                    width=s["width"], height=s["height"],
                    color=tuple(s["color"]),
                    food_categories=set(s.get("food_categories", ["pizza"])),
                    popularity=s.get("popularity", 0.5),
                    service_time=s.get("service_time", 6.0),
                    capacity=s.get("capacity", 3),
                    queue_direction=s.get("queue_direction", "down")
                )
                self.stations.append(station)

            for t in data.get("tables", []):
                self.tables.append(Table(x=t["x"], y=t["y"], seats=t.get("seats", 4)))

            for w in data.get("walls", []):
                self.walls.append(Wall(x1=w["x1"], y1=w["y1"], x2=w["x2"], y2=w["y2"]))

            for e in data.get("entrances", []):
                self.entrances.append(Entrance(x=e["x"], y=e["y"]))

            for e in data.get("exits", []):
                self.exits.append(Exit(x=e["x"], y=e["y"]))

            for d in data.get("dish_returns", []):
                self.dish_returns.append(DishReturn(
                    x=d["x"], y=d["y"],
                    width=d.get("width", 60), height=d.get("height", 40)
                ))

            self.update_pathfinding()
            print(f"Loaded: {len(self.stations)} stations, {len(self.walls)} walls")

        except Exception as e:
            print(f"Error loading layout: {e}")

    def save_layout(self):
        data = {
            "background_image": self.background_path,
            "stations": [
                {
                    "name": s.name, "x": s.x, "y": s.y,
                    "width": s.width, "height": s.height,
                    "color": list(s.color),
                    "food_categories": list(s.food_categories),
                    "popularity": s.popularity,
                    "service_time": s.service_time,
                    "capacity": s.capacity,
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
        print("Layout saved!")

    def update_pathfinding(self):
        self.pathfinder.update_obstacles(self.walls, self.stations)

    def spawn_student(self, entrance: Entrance):
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
            x=entrance.x + random.randint(-8, 8),
            y=entrance.y + random.randint(-8, 8),
            diet=diet,
            speed=random.uniform(STUDENT_SPEED * 0.85, STUDENT_SPEED * 1.15)
        )
        self.student_id_counter += 1
        self.students.append(student)

    def get_compatible_stations(self, student: Student, include_dessert=False) -> List[Station]:
        stations = []
        for s in self.stations:
            if s.is_dessert_station() and not include_dessert:
                continue
            if s.can_serve_diet(student.diet):
                stations.append(s)
        return stations

    def get_dessert_stations(self) -> List[Station]:
        return [s for s in self.stations if s.is_dessert_station()]

    def find_available_table(self) -> Optional[Table]:
        available = [t for t in self.tables if t.has_space]
        if available:
            occupied = [t for t in available if len(t.occupied_by) > 0]
            if occupied and random.random() < 0.6:
                return random.choice(occupied)
            return random.choice(available)
        return None

    def find_nearest_dish_return(self, pos) -> Optional[DishReturn]:
        if not self.dish_returns:
            return None
        return min(self.dish_returns, key=lambda d:
            math.sqrt((d.center[0] - pos[0])**2 + (d.center[1] - pos[1])**2))

    def find_nearest_exit(self, pos) -> Optional[Exit]:
        if not self.exits:
            return None
        return min(self.exits, key=lambda e:
            math.sqrt((e.x - pos[0])**2 + (e.y - pos[1])**2))

    def choose_station(self, student: Student) -> Optional[Station]:
        compatible = self.get_compatible_stations(student)
        if not compatible:
            return None

        # Score stations based on popularity and queue length
        scored = []
        for station in compatible:
            queue_len = len(station.queue) + len(station.being_served)

            # Base score from popularity (higher = more likely to be chosen)
            score = station.popularity * 100

            # Penalty for long queues
            score -= queue_len * 12

            # Random factor for variety
            score += random.randint(-15, 15)

            scored.append((score, station))

        scored.sort(reverse=True, key=lambda x: x[0])

        # Weighted random selection from top choices
        if len(scored) > 1 and random.random() < 0.3:
            return scored[random.randint(0, min(2, len(scored)-1))][1]
        return scored[0][1]

    def apply_separation(self, student: Student):
        sep_x, sep_y = 0, 0

        for other in self.students:
            if other.id == student.id or other.state == StudentState.EXITED:
                continue
            if other.state == StudentState.EATING:
                continue

            dx = student.x - other.x
            dy = student.y - other.y
            dist = math.sqrt(dx*dx + dy*dy)

            if dist < SEPARATION_RADIUS and dist > 0.1:
                force = (SEPARATION_RADIUS - dist) / SEPARATION_RADIUS
                sep_x += (dx / dist) * force
                sep_y += (dy / dist) * force

        student.vx += sep_x * SEPARATION_FORCE
        student.vy += sep_y * SEPARATION_FORCE

    def apply_wall_avoidance(self, student: Student):
        """Push students away from walls"""
        for wall in self.walls:
            rect = wall.get_expanded_rect(WALL_AVOIDANCE_RADIUS)
            if rect.collidepoint(student.x, student.y):
                # Find closest point on wall and push away
                wall_rect = wall.get_rect()
                cx = max(wall_rect.left, min(student.x, wall_rect.right))
                cy = max(wall_rect.top, min(student.y, wall_rect.bottom))

                dx = student.x - cx
                dy = student.y - cy
                dist = math.sqrt(dx*dx + dy*dy)

                if dist > 0 and dist < WALL_AVOIDANCE_RADIUS:
                    force = (WALL_AVOIDANCE_RADIUS - dist) / WALL_AVOIDANCE_RADIUS
                    student.vx += (dx / dist) * force * WALL_AVOIDANCE_FORCE
                    student.vy += (dy / dist) * force * WALL_AVOIDANCE_FORCE

    def check_wall_collision(self, x: float, y: float) -> bool:
        for wall in self.walls:
            rect = wall.get_rect().inflate(STUDENT_RADIUS * 2, STUDENT_RADIUS * 2)
            if rect.collidepoint(x, y):
                return True
        return False

    def move_student_toward(self, student: Student, target: Tuple[float, float]) -> bool:
        if student.path:
            next_point = student.path[0]
            dx = next_point[0] - student.x
            dy = next_point[1] - student.y
            dist = math.sqrt(dx*dx + dy*dy)

            if dist < student.speed * self.speed * 2.5:
                student.path.pop(0)
                if not student.path:
                    student.x, student.y = target
                    student.stuck_timer = 0
                    return True
            else:
                student.vx = (dx / dist) * student.speed
                student.vy = (dy / dist) * student.speed
        else:
            dx = target[0] - student.x
            dy = target[1] - student.y
            dist = math.sqrt(dx*dx + dy*dy)

            if dist < student.speed * self.speed * 2:
                student.x, student.y = target
                student.stuck_timer = 0
                return True

            student.vx = (dx / dist) * student.speed
            student.vy = (dy / dist) * student.speed

        self.apply_separation(student)
        self.apply_wall_avoidance(student)

        new_x = student.x + student.vx * self.speed
        new_y = student.y + student.vy * self.speed

        if not self.check_wall_collision(new_x, new_y):
            old_x, old_y = student.x, student.y
            student.x = new_x
            student.y = new_y

            # Check if stuck
            if abs(student.x - old_x) < 0.1 and abs(student.y - old_y) < 0.1:
                student.stuck_timer += 1
            else:
                student.stuck_timer = 0
        else:
            # Try sliding
            if not self.check_wall_collision(new_x, student.y):
                student.x = new_x
                student.stuck_timer = 0
            elif not self.check_wall_collision(student.x, new_y):
                student.y = new_y
                student.stuck_timer = 0
            else:
                student.stuck_timer += 1

        # If stuck too long, recalculate path
        if student.stuck_timer > 60 and student.target:
            student.path = self.pathfinder.find_path(student.pos, student.target)
            student.stuck_timer = 0

        # Clamp to play area
        student.x = max(STUDENT_RADIUS, min(self.play_area.width - STUDENT_RADIUS, student.x))
        student.y = max(STUDENT_RADIUS, min(WINDOW_HEIGHT - STUDENT_RADIUS, student.y))

        return False

    def update_student(self, student: Student):
        student.time_in_system += 1

        if student.state == StudentState.ENTERING:
            station = self.choose_station(student)
            if station:
                student.target_station = station
                queue_pos = station.get_queue_positions(len(station.queue) + 1)[-1]
                student.target = queue_pos
                student.path = self.pathfinder.find_path(student.pos, queue_pos)
                student.state = StudentState.WALKING_TO_STATION
            elif self.exits:
                exit_point = self.find_nearest_exit(student.pos)
                student.target = exit_point.center
                student.path = self.pathfinder.find_path(student.pos, student.target)
                student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_STATION:
            if self.move_student_toward(student, student.target):
                student.target_station.queue.append(student)
                student.state = StudentState.QUEUING

        elif student.state == StudentState.QUEUING:
            student.wait_time += 1
            station = student.target_station

            if student in station.queue:
                idx = station.queue.index(student)
                positions = station.get_queue_positions(len(station.queue))
                if idx < len(positions):
                    self.move_student_toward(student, positions[idx])

            if student in station.queue[:station.capacity]:
                if len(station.being_served) < station.capacity:
                    station.queue.remove(student)
                    station.being_served.append(student)
                    station.service_timers[student.id] = station.service_time * SERVICE_TIME_MULTIPLIER
                    student.state = StudentState.BEING_SERVED

        elif student.state == StudentState.BEING_SERVED:
            station = student.target_station
            service_positions = station.service_positions
            if station.being_served and student in station.being_served:
                idx = station.being_served.index(student)
                if idx < len(service_positions):
                    self.move_student_toward(student, service_positions[idx])

            if student.id in station.service_timers:
                station.service_timers[student.id] -= self.speed
                if station.service_timers[student.id] <= 0:
                    if student in station.being_served:
                        station.being_served.remove(student)
                    del station.service_timers[student.id]
                    student.has_food = True
                    student.meals_eaten += 1

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
            if student.seat_position:
                self.move_student_toward(student, student.seat_position)

            if student.eat_timer <= 0:
                student.has_food = False
                if student.target_table and student in student.target_table.occupied_by:
                    student.target_table.occupied_by.remove(student)

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

                dish_return = self.find_nearest_dish_return(student.pos)
                if dish_return:
                    queue_pos = dish_return.get_queue_positions(len(dish_return.queue) + 1)[-1]
                    student.target = queue_pos
                    student.path = self.pathfinder.find_path(student.pos, student.target)
                    student.state = StudentState.WALKING_TO_DISH_RETURN
                else:
                    exit_point = self.find_nearest_exit(student.pos)
                    if exit_point:
                        student.target = exit_point.center
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.WALKING_TO_DISH_RETURN:
            if self.move_student_toward(student, student.target):
                for dr in self.dish_returns:
                    dist = math.sqrt((dr.center[0] - student.x)**2 + (dr.center[1] - student.y)**2)
                    if dist < 50:
                        dr.queue.append(student)
                        student.state = StudentState.QUEUING_DISH_RETURN
                        break
                else:
                    exit_point = self.find_nearest_exit(student.pos)
                    if exit_point:
                        student.target = exit_point.center
                        student.path = self.pathfinder.find_path(student.pos, student.target)
                        student.state = StudentState.WALKING_TO_EXIT

        elif student.state == StudentState.QUEUING_DISH_RETURN:
            student.wait_time += 1
            for dr in self.dish_returns:
                if student in dr.queue:
                    idx = dr.queue.index(student)
                    positions = dr.get_queue_positions(len(dr.queue))
                    if idx < len(positions):
                        self.move_student_toward(student, positions[idx])
                    if idx < dr.capacity and len(dr.being_served) < dr.capacity:
                        dr.queue.remove(student)
                        dr.being_served.append(student)
                        student.eat_timer = DISH_RETURN_TIME
                        student.state = StudentState.RETURNING_DISHES
                    break

        elif student.state == StudentState.RETURNING_DISHES:
            student.eat_timer -= self.speed
            for dr in self.dish_returns:
                if student in dr.being_served:
                    self.move_student_toward(student, dr.center)
                    break
            if student.eat_timer <= 0:
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
        if self.paused or self.editor_mode:
            return

        self.frame_count += 1

        for entrance in self.entrances:
            spawn_rate = max(1, int(entrance.spawn_rate / self.speed))
            if self.frame_count % spawn_rate == 0:
                self.spawn_student(entrance)

        for student in self.students:
            if student.state != StudentState.EXITED:
                self.update_student(student)

        exited = [s for s in self.students if s.state == StudentState.EXITED]
        if len(exited) > 50:
            for s in exited[:-50]:
                self.students.remove(s)

    def draw(self):
        # Background
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

        # Entrances
        for entrance in self.entrances:
            pygame.draw.circle(self.screen, COLORS["entrance"], entrance.center, 18)
            pygame.draw.circle(self.screen, (255, 255, 255), entrance.center, 18, 2)
            text = self.small_font.render("IN", True, COLORS["text_dark"])
            self.screen.blit(text, (entrance.x - 7, entrance.y - 5))

        # Exits
        for exit_point in self.exits:
            pygame.draw.circle(self.screen, COLORS["exit"], exit_point.center, 18)
            pygame.draw.circle(self.screen, (255, 255, 255), exit_point.center, 18, 2)
            text = self.small_font.render("OUT", True, COLORS["text_dark"])
            self.screen.blit(text, (exit_point.x - 11, exit_point.y - 5))

        # Dish returns
        for dr in self.dish_returns:
            pygame.draw.rect(self.screen, COLORS["dish_return"],
                           pygame.Rect(dr.x, dr.y, dr.width, dr.height))
            pygame.draw.rect(self.screen, (255, 255, 255),
                           pygame.Rect(dr.x, dr.y, dr.width, dr.height), 2)
            text = self.small_font.render("DISHES", True, COLORS["text_dark"])
            self.screen.blit(text, (dr.x + 3, dr.y + dr.height//2 - 5))
            if dr.queue:
                q_text = self.small_font.render(f"Q:{len(dr.queue)}", True, COLORS["text"])
                self.screen.blit(q_text, (dr.x, dr.y + dr.height + 3))

        # Tables
        for table in self.tables:
            color = COLORS["table_occupied"] if table.occupied_by else COLORS["table"]
            pygame.draw.circle(self.screen, color, table.center, 20)
            pygame.draw.circle(self.screen, (180, 180, 180), table.center, 20, 2)
            text = self.small_font.render(f"{len(table.occupied_by)}/{table.seats}", True, COLORS["text"])
            self.screen.blit(text, (table.x - 10, table.y - 5))

        # Stations
        for station in self.stations:
            # Highlight if selected
            if station == self.selected_station:
                highlight_rect = pygame.Rect(station.x - 3, station.y - 3,
                                            station.width + 6, station.height + 6)
                pygame.draw.rect(self.screen, COLORS["selected"], highlight_rect, 3)

            pygame.draw.rect(self.screen, station.color,
                           pygame.Rect(station.x, station.y, station.width, station.height))
            pygame.draw.rect(self.screen, (255, 255, 255),
                           pygame.Rect(station.x, station.y, station.width, station.height), 2)

            # Name
            text = self.small_font.render(station.name[:12], True, COLORS["text_dark"])
            self.screen.blit(text, (station.x + 3, station.y + 3))

            # Queue
            queue_len = len(station.queue)
            if queue_len > 0:
                q_color = (255, 100, 100) if queue_len > 5 else COLORS["text"]
                q_text = self.small_font.render(f"Q:{queue_len}", True, q_color)
                self.screen.blit(q_text, (station.x, station.y + station.height + 3))

        # Students
        for student in self.students:
            if student.state == StudentState.EXITED:
                continue
            pygame.draw.circle(self.screen, student.color,
                             (int(student.x), int(student.y)), STUDENT_RADIUS)
            if student.has_food:
                pygame.draw.circle(self.screen, COLORS["student_has_food"],
                                 (int(student.x), int(student.y)), 2)

        # UI
        self.draw_ui()

        # Properties panel
        self.properties_panel.draw(self.screen)

        pygame.display.flip()

    def draw_ui(self):
        # Stats panel
        active = len([s for s in self.students if s.state != StudentState.EXITED])
        avg_wait = (self.total_wait_time / max(1, self.total_students_served)) / 60
        avg_time = (self.total_time_in_system / max(1, self.total_students_served)) / 60

        panel = pygame.Rect(5, 5, 200, 140)
        pygame.draw.rect(self.screen, COLORS["ui_bg"], panel)
        pygame.draw.rect(self.screen, (80, 80, 80), panel, 1)

        stats = [
            f"Active: {active} | Served: {self.total_students_served}",
            f"Avg Wait: {avg_wait:.1f}s | Total: {avg_time:.1f}s",
            f"Speed: {self.speed:.1f}x",
            "",
            "SPACE=Run  E=Edit  R=Reset",
            "+/- Speed  S=Save  L=Image"
        ]

        if self.paused and not self.editor_mode:
            stats.insert(0, "[ PAUSED ]")
        elif self.editor_mode:
            stats.insert(0, "[ EDITOR ]")

        y = 10
        for stat in stats:
            text = self.small_font.render(stat, True, COLORS["text"])
            self.screen.blit(text, (10, y))
            y += 16

        # Bottleneck warnings
        y_warn = 160
        for station in self.stations:
            if len(station.queue) > 5:
                warn = f"! {station.name}: {len(station.queue)} waiting"
                text = self.font.render(warn, True, (255, 100, 100))
                pygame.draw.rect(self.screen, (40, 0, 0), (5, y_warn, text.get_width() + 10, 22))
                self.screen.blit(text, (10, y_warn + 2))
                y_warn += 25

        if self.editor_mode:
            self.draw_editor_toolbar()

    def draw_editor_toolbar(self):
        toolbar_y = WINDOW_HEIGHT - 55
        toolbar_rect = pygame.Rect(0, toolbar_y, self.play_area.width, 55)
        pygame.draw.rect(self.screen, COLORS["ui_bg"], toolbar_rect)
        pygame.draw.line(self.screen, (80, 80, 80), (0, toolbar_y), (self.play_area.width, toolbar_y))

        tools = [
            (EditorTool.SELECT, "0:Select"),
            (EditorTool.STATION, "1:Station"),
            (EditorTool.TABLE, "2:Table"),
            (EditorTool.WALL, "3:Wall"),
            (EditorTool.ENTRANCE, "4:Enter"),
            (EditorTool.EXIT, "5:Exit"),
            (EditorTool.DISH_RETURN, "6:Dishes"),
        ]

        x = 15
        for tool, label in tools:
            is_active = self.current_tool == tool
            color = COLORS["button_active"] if is_active else COLORS["button"]
            btn = pygame.Rect(x, toolbar_y + 8, 80, 38)
            pygame.draw.rect(self.screen, color, btn, border_radius=4)
            pygame.draw.rect(self.screen, (120, 120, 120) if is_active else (80, 80, 80), btn, 1, border_radius=4)
            text = self.small_font.render(label, True, COLORS["text"])
            self.screen.blit(text, (x + 8, toolbar_y + 18))
            x += 88

        # Help text
        help_text = "DEL=Delete  C=Clear  Click station to edit properties"
        text = self.small_font.render(help_text, True, COLORS["text_muted"])
        self.screen.blit(text, (x + 20, toolbar_y + 20))

    def get_item_at(self, pos) -> tuple:
        x, y = pos
        for station in self.stations:
            if station.x <= x <= station.x + station.width:
                if station.y <= y <= station.y + station.height:
                    return ("station", station)
        for table in self.tables:
            if math.sqrt((table.x - x)**2 + (table.y - y)**2) < 22:
                return ("table", table)
        for wall in self.walls:
            if wall.get_rect().collidepoint(x, y):
                return ("wall", wall)
        for entrance in self.entrances:
            if math.sqrt((entrance.x - x)**2 + (entrance.y - y)**2) < 20:
                return ("entrance", entrance)
        for exit_point in self.exits:
            if math.sqrt((exit_point.x - x)**2 + (exit_point.y - y)**2) < 20:
                return ("exit", exit_point)
        for dr in self.dish_returns:
            if dr.x <= x <= dr.x + dr.width and dr.y <= y <= dr.y + dr.height:
                return ("dish_return", dr)
        return (None, None)

    def handle_editor_click(self, pos, button):
        if button != 1:
            return

        # Check if clicking on properties panel
        if self.properties_panel.visible and self.properties_panel.rect.collidepoint(pos):
            return

        if self.current_tool == EditorTool.SELECT:
            item_type, item = self.get_item_at(pos)
            if item_type == "station":
                self.selected_station = item
                self.properties_panel.show(item)
            else:
                self.selected_station = None
                self.properties_panel.hide()

        elif self.current_tool in [EditorTool.STATION, EditorTool.WALL, EditorTool.DISH_RETURN]:
            self.drawing = True
            self.draw_start = pos

        elif self.current_tool == EditorTool.TABLE:
            self.tables.append(Table(x=pos[0], y=pos[1], seats=4))

        elif self.current_tool == EditorTool.ENTRANCE:
            self.entrances.append(Entrance(x=pos[0], y=pos[1]))

        elif self.current_tool == EditorTool.EXIT:
            self.exits.append(Exit(x=pos[0], y=pos[1]))

    def handle_editor_release(self, pos):
        if not self.drawing or not self.draw_start:
            return

        x = min(self.draw_start[0], pos[0])
        y = min(self.draw_start[1], pos[1])
        w = abs(pos[0] - self.draw_start[0])
        h = abs(pos[1] - self.draw_start[1])

        if self.current_tool == EditorTool.STATION and w > 20 and h > 20:
            color = (random.randint(150, 240), random.randint(150, 240), random.randint(100, 200))
            station = Station(
                name=f"Station {len(self.stations) + 1}",
                x=x, y=y, width=w, height=h,
                color=color
            )
            self.stations.append(station)
            self.selected_station = station
            self.properties_panel.show(station)
            self.update_pathfinding()

        elif self.current_tool == EditorTool.WALL and (w > 5 or h > 5):
            self.walls.append(Wall(x1=self.draw_start[0], y1=self.draw_start[1],
                                  x2=pos[0], y2=pos[1]))
            self.update_pathfinding()

        elif self.current_tool == EditorTool.DISH_RETURN and w > 20 and h > 20:
            self.dish_returns.append(DishReturn(x=x, y=y, width=w, height=h))

        self.drawing = False
        self.draw_start = None

    def delete_at(self, pos):
        item_type, item = self.get_item_at(pos)
        if item_type == "station":
            if self.selected_station == item:
                self.selected_station = None
                self.properties_panel.hide()
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
        self.stations = []
        self.tables = []
        self.walls = []
        self.entrances = []
        self.exits = []
        self.dish_returns = []
        self.selected_station = None
        self.properties_panel.hide()
        self.reset_simulation()
        self.update_pathfinding()
        print("Layout cleared!")

    def run(self):
        print("=" * 60)
        print("DINING HALL FLOW SIMULATOR v2.1")
        print("=" * 60)
        print("Press L to load your dining hall image")
        print("Use tools 0-6 to place elements")
        print("Click a station to edit its properties")
        print("Press SPACE to start simulation")
        print("=" * 60)

        while self.running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.running = False

                # Let properties panel handle events first
                if self.properties_panel.handle_event(event):
                    continue

                if event.type == pygame.KEYDOWN:
                    if event.key in [pygame.K_ESCAPE, pygame.K_q]:
                        self.running = False

                    elif event.key == pygame.K_SPACE:
                        if self.editor_mode:
                            self.editor_mode = False
                            self.paused = False
                            self.properties_panel.hide()
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
                        self.delete_at(pygame.mouse.get_pos())

                    # Tool selection
                    elif self.editor_mode:
                        if event.key == pygame.K_0:
                            self.current_tool = EditorTool.SELECT
                        elif event.key == pygame.K_1:
                            self.current_tool = EditorTool.STATION
                        elif event.key == pygame.K_2:
                            self.current_tool = EditorTool.TABLE
                        elif event.key == pygame.K_3:
                            self.current_tool = EditorTool.WALL
                        elif event.key == pygame.K_4:
                            self.current_tool = EditorTool.ENTRANCE
                        elif event.key == pygame.K_5:
                            self.current_tool = EditorTool.EXIT
                        elif event.key == pygame.K_6:
                            self.current_tool = EditorTool.DISH_RETURN

                elif event.type == pygame.MOUSEBUTTONDOWN and self.editor_mode:
                    if event.pos[1] < WINDOW_HEIGHT - 55 and event.pos[0] < self.play_area.width:
                        self.handle_editor_click(event.pos, event.button)

                elif event.type == pygame.MOUSEBUTTONUP and self.editor_mode:
                    self.handle_editor_release(event.pos)

            self.update()
            self.draw()

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
