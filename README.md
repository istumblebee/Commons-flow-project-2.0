# Dining Hall Flow Simulator

An agent-based simulation to identify bottlenecks in dining hall flow. Think RollerCoaster Tycoon but for your college dining hall.

## Quick Start

### 1. Install Python (if you don't have it)

**Windows:**
- Download from https://www.python.org/downloads/
- During install, CHECK "Add Python to PATH"

**Mac:**
```bash
brew install python
```

**Linux:**
```bash
sudo apt install python3 python3-pip
```

### 2. Install Dependencies

```bash
cd Commons-flow-project-2.0
pip install -r requirements.txt
```

### 3. Add Your Dining Hall Image

Put your dining hall floor plan image at:
```
assets/dining_hall.png
```

The image will be scaled to 900x600 pixels.

### 4. Run the Simulation

```bash
python dining_sim.py
```

## Controls

| Key | Action |
|-----|--------|
| SPACE | Pause/Resume simulation |
| E | Toggle Editor mode |
| +/- | Speed up/slow down |
| S | Save station layout |
| R | Reset simulation |
| Q/ESC | Quit |

### Editor Mode (press E)

| Action | What it does |
|--------|--------------|
| Click + Drag | Draw a new food station |
| T | Place a table at cursor |
| D | Place dish return at cursor |
| Right-Click | Delete item under cursor |
| S | Save your layout |

## How Students Work

Each student dot is an autonomous agent with:
- **Dietary preference** (omnivore, vegetarian, vegan)
- **Behavior type** (goes straight to food OR browses first)
- **Decision making** (prefers shorter queues)

### Student Flow:
1. Enter venue
2. Either browse or go directly to a compatible station
3. Wait in queue
4. Get served (takes time based on station)
5. Find a table and eat (10-20 min simulated)
6. Maybe get seconds or dessert (configurable chance)
7. Return dishes
8. Exit

## Customizing

### Edit `config/stations.json` to:
- Change station names, positions, sizes
- Set food types: `"meat"`, `"vegetarian"`, `"vegan"`, `"all"`, `"dessert"`
- Adjust service times and capacity
- Add/remove tables

### Edit the top of `dining_sim.py` to:
- Change spawn rates
- Adjust dietary distribution
- Modify eating times
- Change colors

## Finding Bottlenecks

The simulation shows:
- **Queue lengths** under each station
- **Average wait time** in the stats panel
- **Bottleneck warnings** when queues get long
- **Average time in system** (total time from entry to exit)

Red warning = that station is a bottleneck!

## Student Color Coding

- **Yellow** = Omnivore
- **Light Green** = Vegetarian
- **Bright Green** = Vegan
- **Brown dot in center** = Student has food
