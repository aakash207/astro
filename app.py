import streamlit as st
from datetime import datetime, timedelta
from math import sin, cos, tan, atan2, degrees, radians
from astropy.time import Time
from astropy.coordinates import get_body, solar_system_ephemeris, GeocentricTrueEcliptic
from collections import defaultdict
import pandas as pd
from geopy.geocoders import Nominatim
from geopy.extra.rate_limiter import RateLimiter
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import io
import copy
# NEW: timezone detection for "Current City"
from timezonefinder import TimezoneFinder
import pytz

# ---- Matplotlib defaults (crisp + thin) ----
plt.rcParams.update({"figure.dpi": 300, "savefig.dpi": 300, "lines.linewidth": 0.28})

# ---- Constants ----
cities_fallback = {
    'Chennai': {'lat': 13.08, 'lon': 80.27}, 'Mumbai': {'lat': 19.07, 'lon': 72.88},
    'Delhi': {'lat': 28.61, 'lon': 77.23}, 'Bangalore': {'lat': 12.97, 'lon': 77.59},
    'Kolkata': {'lat': 22.57, 'lon': 88.36}, 'Hyderabad': {'lat': 17.39, 'lon': 78.49},
}
sign_names = ['Aries','Taurus','Gemini','Cancer','Leo','Virgo','Libra','Scorpio','Sagittarius','Capricorn','Aquarius','Pisces']

# Mapping for Tamil sign names used in status calculation
tamil_to_english = {
    'Mesham': 'Aries', 'Rishabam': 'Taurus', 'Mithunam': 'Gemini', 'Kadagam': 'Cancer',
    'Simmam': 'Leo', 'Kanni': 'Virgo', 'Thulam': 'Libra', 'Viruchigam': 'Scorpio',
    'Dhanusu': 'Sagittarius', 'Magaram': 'Capricorn', 'Kumbam': 'Aquarius', 'Meenam': 'Pisces'
}

lords_full = ['Ketu','Venus','Sun','Moon','Mars','Rahu','Jupiter','Saturn','Mercury']
lords_short = ['Ke','Ve','Su','Mo','Ma','Ra','Ju','Sa','Me']
nak_names = ['Ashwini','Bharani','Krittika','Rohini','Mrigashira','Ardra','Punarvasu','Pushya','Ashlesha',
             'Magha','Purva Phalguni','Uttara Phalguni','Hasta','Chitra','Swati','Vishakha','Anuradha',
             'Jyeshta','Mula','Purva Ashadha','Uttara Ashadha','Shravana','Dhanishta','Shatabhisha',
             'Purva Bhadrapada','Uttara Bhadrapada','Revati']
years = [7, 20, 6, 10, 7, 18, 16, 19, 17] * 3
sign_lords = ['Mars','Venus','Mercury','Moon','Sun','Mercury','Venus','Mars','Jupiter','Saturn','Saturn','Jupiter']

sthana_bala_dict = {
    'Sun': [100,90,80,70,60,50,40,50,60,70,80,90],
    'Moon': [90,100,90,80,70,60,60,50,70,70,70,90],
    'Jupiter': [60,60,70,100,90,60,75,60,80,40,50,80],
    'Venus': [60,70,60,50,40,35,80,50,60,80,70,100],
    'Mercury': [40,60,70,45,60,100,60,45,55,50,45,35],
    'Mars': [80,70,45,35,60,45,50,60,60,100,90,60],
    'Saturn': [35,50,60,70,80,60,100,90,50,60,80,50],
    'Rahu': [100]*12,
    'Ketu': [100]*12
}

# Status Mapping
status_data = {
    'Sun': {'Uchcham': 'Aries', 'Moolathirigonam': None, 'Aatchi': 'Leo', 'Neecham': 'Libra'},
    'Moon': {'Uchcham': 'Taurus', 'Moolathirigonam': None, 'Aatchi': 'Cancer', 'Neecham': 'Scorpio'},
    'Jupiter': {'Uchcham': 'Cancer', 'Moolathirigonam': 'Sagittarius', 'Aatchi': 'Pisces', 'Neecham': 'Capricorn'},
    'Venus': {'Uchcham': 'Pisces', 'Moolathirigonam': 'Libra', 'Aatchi': 'Taurus', 'Neecham': 'Virgo'},
    'Mercury': {'Uchcham': 'Virgo', 'Moolathirigonam': None, 'Aatchi': 'Gemini', 'Neecham': 'Pisces'},
    'Mars': {'Uchcham': 'Capricorn', 'Moolathirigonam': 'Aries', 'Aatchi': 'Scorpio', 'Neecham': 'Cancer'},
    'Saturn': {'Uchcham': 'Libra', 'Moolathirigonam': 'Aquarius', 'Aatchi': 'Capricorn', 'Neecham': 'Aries'}
}

# Capacity percentages
capacity_dict = {
    'Saturn': 100, 'Mars': 50, 'Sun': 100, 'Jupiter': 100, 
    'Venus': 50, 'Mercury': 30, 'Moon': 100, 'Rahu': 100, 'Ketu': 50
}
# Good/Bad percentages
good_capacity_dict = {
    'Saturn': 0, 'Mars': 75, 'Sun': 50, 'Jupiter': 100, 
    'Venus': 100, 'Mercury': 100, 'Rahu': 0, 'Ketu': 100
}
bad_capacity_dict = {
    'Saturn': 100, 'Mars': 25, 'Sun': 50, 'Jupiter': 0, 
    'Venus': 0, 'Mercury': 0, 'Rahu': 100, 'Ketu': 0
}

# Degree Gap Limits
mix_dict = {0:100,1:100,2:100,3:95,4:90,5:85,6:80,7:75,8:70,9:65,10:60,11:55,12:50,13:45,14:40,15:35,16:30,17:25,18:20,19:15,20:10,21:5,22:0}

# Moon Tithi Capacities
shukla_good = [100, 9, 16, 23, 30, 37, 44, 51, 58, 65, 72, 79, 86, 93, 100]
shukla_bad = [0] * 15
krishna_good = [93, 86, 79, 72, 65, 58, 51, 44, 37, 30, 23, 16, 9, 2, 0]
krishna_bad = [7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98, 100]

# Single currency planets
single_currency_planets = ['Venus', 'Jupiter', 'Mercury', 'Rahu', 'Ketu', 'Saturn']

# Base Malefics
base_malefics = ['Saturn', 'Mars', 'Sun', 'Rahu']

# ---- Astro helpers ----
def get_lahiri_ayanamsa(year):
    base = 23.853; rate = 50.2388/3600.0
    return (base + (year - 2000) * rate) % 360

def get_obliquity(d):
    T = d/36525.0
    return ((((-4.34e-8*T - 5.76e-7)*T + 0.0020034)*T - 1.831e-4)*T - 46.836769)*T/3600 + 23.4392794444444

def get_gmst(d):
    T = d/36525.0
    return (67310.54841 + (3155760000 + 8640184.812866)*T + 0.093104*T**2 - 6.2e-6*T**3)/3600 % 24

def get_ascendant(jd, lat, lon):
    d = jd - 2451545.0
    oer = radians(get_obliquity(d))
    lst = (get_gmst(d) + lon/15.0) % 24
    lstr = radians(lst*15.0)
    sin_asc = cos(lstr)
    cos_asc = -(sin(lstr)*cos(oer) + tan(radians(lat))*sin(oer))
    return degrees(atan2(sin_asc, cos_asc)) % 360

def get_sidereal_lon(tlon, ayan): return (tlon - ayan) % 360
def get_sign(lon): return sign_names[int(lon/30)]
def get_house(lon, lagna_lon): return (int(lon/30) - int(lagna_lon/30)) % 12 + 1

def get_nakshatra_details(lon):
    dnak = 360/27
    idx = int(lon // dnak) % 27
    pos = lon % dnak
    pada = int((pos/(dnak/4))) + 1
    star = idx % 9
    sub = (star + int((pos/dnak)*9)) % 9
    return nak_names[idx], pada, lords_short[star], lords_short[sub]

def generate_vimshottari_dasa(moon_lon):
    nak = int(moon_lon * 27 / 360)
    lord_idx = nak % 9
    y = years[lord_idx]
    pos_in_nak = moon_lon % (360/27)
    fraction = pos_in_nak / (360/27)
    return lord_idx, y * (1 - fraction)

def generate_periods(start_date, lord_idx, total_years, level='dasa', max_depth=3):
    periods, remaining, i, current = [], total_years, lord_idx, start_date
    depth_map = {'dasa':0,'bhukti':1,'anthara':2,'sukshma':3,'prana':4,'sub_prana':5}
    next_level = {0:'bhukti',1:'anthara',2:'sukshma',3:'prana',4:'sub_prana',5:None}
    depth = depth_map.get(level,0)
    while remaining > 0:
        lord = lords_full[i]; y_full = years[i]
        y = min((y_full/120)*total_years, remaining)
        end = current + timedelta(days=y*365.25)
        subs = generate_periods(current, i, y, next_level[depth], max_depth) if (depth < max_depth-1 and next_level[depth]) else []
        periods.append((lord, current, end, subs))
        remaining -= y; current = end; i = (i+1) % 9
    return periods

def filter_from_birth(periods, birth_dt):
    out = []
    for lord, start, end, sub in periods:
        if end > birth_dt:
            out.append((lord, max(start, birth_dt), end, filter_from_birth(sub, birth_dt) if sub else []))
    return out

def duration_str(delta, level='dasa'):
    days = delta.total_seconds()/86400
    if days < 1 and level in ['sukshma','prana','sub_prana']:
        hrs = days*24; h = int(hrs); m = int((hrs - h)*60)
        return "Less than 1 minute" if h==0 and m==0 else f"{h}h {m}m"
    y = int(days/365.25); rem = days % 365.25
    m = int(rem/30.4375); d = int(rem % 30.4375)
    return "Less than 1 day" if y+m+d==0 else f"{y}y {m}m {d}d"

def calculate_dig_bala(planet, lon, lagna):
    east = lagna % 360
    north = (lagna + 90) % 360
    west = (lagna + 180) % 360
    south = (lagna + 270) % 360
    if planet.lower() in ['sun', 'mars']:
        D = north
    elif planet.lower() in ['moon', 'venus']:
        D = south
    elif planet.lower() in ['mercury', 'jupiter', 'ketu']:
        D = west
    elif planet.lower() in ['saturn', 'rahu']:
        D = east
    else:
        return None
    diff = abs(lon - D)
    ang_dist = min(diff, 360 - diff)
    virupas = ang_dist / 3
    percentage = (virupas / 60) * 100
    return round(percentage, 2)

def compute_chart(name, date_obj, time_str, lat, lon, tz_offset, max_depth):
    # parse time
    try:
        hour, minute = map(int, time_str.split(':'))
        if not (0<=hour<=23 and 0<=minute<=59): raise ValueError
    except:
        raise ValueError("Time must be in HH:MM format (24-hour)")
    
    local_dt = datetime.combine(date_obj, datetime.min.time().replace(hour=hour, minute=minute))
    utc_dt = local_dt - timedelta(hours=tz_offset)
    t = Time(utc_dt); jd = t.jd; ayan = get_lahiri_ayanamsa(utc_dt.year)
    
    with solar_system_ephemeris.set('builtin'):
        lon_trop = {}
        for nm in ['sun','moon','mercury','venus','mars','jupiter','saturn']:
            ecl = get_body(nm, t).transform_to(GeocentricTrueEcliptic()); lon_trop[nm] = ecl.lon.deg
    
    d = jd - 2451545.0; T = d/36525.0
    omega = (125.04452 - 1934.136261*T + 0.0020708*T**2 + T**3/450000) % 360
    lon_trop['rahu'] = omega; lon_trop['ketu'] = (omega + 180) % 360
    lon_sid = {p: get_sidereal_lon(lon_trop[p], ayan) for p in lon_trop}
    lagna_sid = get_sidereal_lon(get_ascendant(jd, lat, lon), ayan)
    
    # --- Step 1: Identify Moon Phase (Paksha) ---
    sun_lon = lon_sid['sun']
    moon_lon = lon_sid['moon']
    diff = (moon_lon - sun_lon) % 360
    
    if diff < 180: paksha = 'Shukla'
    else: paksha = 'Krishna'

    tithi_fraction = diff / 12
    tithi = int(tithi_fraction) + 1
    if tithi > 30: tithi = 30
    
    if paksha == 'Shukla':
        tithi_idx = tithi - 1
        if tithi_idx > 14: tithi_idx = 14
    else:
        tithi_idx = tithi - 16
        if tithi_idx < 0: tithi_idx = 0
        if tithi_idx > 14: tithi_idx = 14

    # rasi houses
    house_planets_rasi = defaultdict(list)
    positions = {**lon_sid, 'asc': lagna_sid}
    for p, L in positions.items():
        house_planets_rasi[get_house(L, lagna_sid)].append(p.capitalize() if p != 'asc' else 'Asc')

    # Calculate initial values and debt for simulation
    planet_objs = ['Sun','Moon','Mars','Mercury','Jupiter','Venus','Saturn','Rahu','Ketu']
    
    sim_data = {}
    
    for p in planet_objs:
        L = lon_sid[p.lower()]; sign = get_sign(L)
        sthana = sthana_bala_dict.get(p, [0]*12)[sign_names.index(sign)]
        capacity = capacity_dict.get(p, None)
        volume = (capacity * sthana / 100.0) if capacity is not None else 0.0
        
        # Determine Good/Bad Percentages
        if p == 'Moon':
            if paksha == 'Shukla':
                good_pct = shukla_good[tithi_idx]
                bad_pct = shukla_bad[tithi_idx]
            else:
                good_pct = krishna_good[tithi_idx]
                bad_pct = krishna_bad[tithi_idx]
        else:
            good_pct = good_capacity_dict.get(p, 0)
            bad_pct = bad_capacity_dict.get(p, 0)

        good_val = volume * (good_pct / 100.0)
        bad_val = volume * (bad_pct / 100.0)
        
        # Calculate Initial Debt
        debt = 0.0
        is_malefic = False
        if p in base_malefics:
            debt = -bad_val
            is_malefic = True
        elif p == 'Moon' and paksha == 'Krishna':
            debt = -bad_val
            is_malefic = True
            
        if p == 'Ketu':
            debt = -bad_val - 50.0
            is_malefic = True
            
        sim_data[p] = {
            'Good': good_val,
            'Bad': bad_val,
            'Debt': debt,
            'IsMalefic': is_malefic,
            'GoodPct': good_pct,
            'BadPct': bad_pct,
            'Gained': defaultdict(float), # Track what we gained: {'Venus': 20, 'Good Mars': 5}
            'L': L
        }

    # --- Phase One Currency Exchange Simulation ---
    
    # Define Rankings
    # Debtor Rank: Rahu > Sun > Saturn > Mars > Ketu > Waning Moon
    debtor_rank = ['Rahu', 'Sun', 'Saturn', 'Mars', 'Ketu']
    if paksha == 'Krishna':
        debtor_rank.append('Moon')

    # Currency Rank (The Menu)
    # Build list of (PlanetName, Type, SortValue)
    # Type: 'Good' or 'Bad'
    # Good Tier: Sort by GoodPct Descending
    # Bad Tier: Sort by BadPct Ascending (Least bad first)
    
    good_menu = []
    bad_menu = []
    
    for p in planet_objs:
        # Add Good component if > 0
        if sim_data[p]['Good'] > 0 or sim_data[p]['GoodPct'] > 0:
            # Moon special handling for sort value if needed, but percentages work
            good_menu.append((p, 'Good', sim_data[p]['GoodPct']))
            
        # Add Bad component if > 0
        if sim_data[p]['Bad'] > 0 or sim_data[p]['BadPct'] > 0:
            bad_menu.append((p, 'Bad', sim_data[p]['BadPct']))
            
    # Sort Menus
    # Good: Descending %
    good_menu.sort(key=lambda x: x[2], reverse=True)
    # Bad: Ascending %
    bad_menu.sort(key=lambda x: x[2])
    
    full_menu = good_menu + bad_menu # Good First, then Bad
    
    # Limits Tracker: (Debtor, Target) -> AmountPulled
    pulled_amount = defaultdict(float)
    
    # Simulation Loop
    step_size = 1.0
    max_cycles = 1000 # Safety break
    cycle = 0
    
    while cycle < max_cycles:
        moves_made = False
        
        # Check if any debtor still needs to eat
        any_hungry = False
        for debtor in debtor_rank:
            if sim_data[debtor]['Debt'] < -0.001: # Use epsilon for float comparison
                any_hungry = True
                break
        
        if not any_hungry:
            break
            
        for debtor in debtor_rank:
            if sim_data[debtor]['Debt'] >= -0.001:
                continue # Full
            
            # Find best target
            target_found = False
            
            # Scan Menu
            for target_name, curr_type, pct in full_menu:
                if target_name == debtor: continue
                
                # Ketu Rule: Only Sun/Moon
                if debtor == 'Ketu' and target_name not in ['Sun', 'Moon']:
                    continue
                
                # Check Currency Availability
                available = sim_data[target_name][curr_type]
                if available <= 0.001: continue
                
                # Check Connection / Degree Gap
                dist = abs(sim_data[debtor]['L'] - sim_data[target_name]['L'])
                if dist > 180: dist = 360 - dist
                dist_int = int(dist)
                
                limit_pct = mix_dict.get(dist_int, 0)
                if limit_pct == 0: continue # Not reachable
                
                # Check Cap
                # Cap is based on TOTAL volume of target (Initial Good + Initial Bad)
                # Or based on current? "maximum capacity to pull will become 55% it cant pull beyond that"
                # Usually based on Initial total volume of the target.
                # Let's calculate initial total once
                initial_total = (capacity_dict.get(target_name,0) * sthana_bala_dict.get(target_name, [0]*12)[sign_names.index(get_sign(lon_sid[target_name.lower()]))] / 100.0)
                
                max_pullable = initial_total * (limit_pct / 100.0)
                current_pulled = pulled_amount[(debtor, target_name)]
                
                if current_pulled >= max_pullable: continue
                
                # Valid Target Found
                # Determine bite size
                needed = abs(sim_data[debtor]['Debt'])
                bite = min(step_size, available, max_pullable - current_pulled, needed)
                
                if bite <= 0.0001: continue
                
                # Execute Transaction
                
                # 1. Target Loses
                sim_data[target_name][curr_type] -= bite
                # Target Debt Increases (Target becomes debtor if it wasn't, or debt deepens)
                # "Each currency a planet loose ... debt increases"
                # For benefics starting at 0, this makes them negative.
                sim_data[target_name]['Debt'] -= bite 
                
                # 2. Debtor Gains
                # Track inventory
                # Label: "Venus" or "Good Sun" or "Bad Sun"
                label = target_name
                if target_name not in single_currency_planets:
                    label = f"{curr_type} {target_name}"
                
                sim_data[debtor]['Gained'][label] += bite
                
                # Debtor Debt Reduces (for both Good and Bad gain)
                sim_data[debtor]['Debt'] += bite
                
                # 3. Track Cap
                pulled_amount[(debtor, target_name)] += bite
                
                target_found = True
                moves_made = True
                break # Move to next debtor after one bite
            
        if not moves_made:
            break
        cycle += 1

    # --- Formatting Outputs ---
    
    rows = []
    planet_order_final = ['Sun','Moon','Mars','Mercury','Jupiter','Venus','Saturn','Rahu','Ketu']
    
    for p in planet_order_final:
        d = sim_data[p]
        
        # Build Currency Phase 1 String
        # Start with remaining initial holdings
        curr_parts = []
        
        # Remaining Good
        if d['Good'] > 0.01:
            if p in single_currency_planets:
                curr_parts.append(f"{p}[{d['Good']:.2f}]")
            else:
                curr_parts.append(f"Good {p}[{d['Good']:.2f}]")
                
        # Remaining Bad
        if d['Bad'] > 0.01:
            # Check Moon rule: Towards full moon (Shukla) -> no bad currency shown (it was 0 anyway)
            # Just add logic as before
            if not (p == 'Moon' and paksha == 'Shukla'):
                 if p in single_currency_planets:
                     # This case implies single currency planets have bad... 
                     # Saturn/Rahu have 100 bad. They are single currency.
                     # We display them as "Saturn[100]" usually.
                     # The code for single_currency_planets logic in Step 1 was:
                     # if single: Name[Total].
                     # Here split is fine, but let's stick to Name[Val] if it's single
                     # But wait, Single Planets like Saturn only have Bad.
                     curr_parts.append(f"{p}[{d['Bad']:.2f}]")
                 else:
                     curr_parts.append(f"Bad {p}[{d['Bad']:.2f}]")

        # Add Gained
        for label, val in d['Gained'].items():
            if val > 0.01:
                curr_parts.append(f"{label}[{val:.2f}]")
                
        currency_str = ", ".join(curr_parts)
        if not currency_str: currency_str = "-"
        
        # Build Debt Phase 1 String
        # If debt is negative, show it. If >= 0, show - or 0?
        # "If debt reaches 0... show - " for benefics usually?
        # User said: "Just show number in debt column like -50 etc"
        # And "For benefics: Shows - (as they started with 0 debt)" -> But they lose currency now, so they gain debt.
        # "Target looses 1 unit... debt increases" -> Benefics will have negative debt now.
        # So we show the number.
        
        debt_val = d['Debt']
        if abs(debt_val) < 0.01:
            debt_str = "0.00"
        else:
            debt_str = f"{debt_val:.2f}"
            
        # Re-gather basic data for table
        # We need the original computed values from before simulation for the other columns
        L = d['L']
        sign = get_sign(L)
        nak, pada, ld, sl = get_nakshatra_details(L)
        dig_bala = calculate_dig_bala(p, L, lagna_sid)
        sthana = sthana_bala_dict.get(p, [0]*12)[sign_names.index(sign)]
        capacity = capacity_dict.get(p, None)
        vol = (capacity * sthana / 100.0) if capacity is not None else 0.0
        
        # Status
        status = '-'
        if p in status_data:
            mapping = status_data[p]
            if sign == mapping['Uchcham']: status = 'Uchcham'
            elif sign == mapping['Neecham']: status = 'Neecham'
            elif sign == mapping['Moolathirigonam']: status = 'Moolathirigonam'
            elif sign == mapping['Aatchi']: status = 'Aatchi'

        # Default Currencies String (Pre-Simulation)
        # Re-calc for display
        def_parts = []
        g_orig = vol * (d['GoodPct']/100.0)
        b_orig = vol * (d['BadPct']/100.0)
        
        if p in single_currency_planets:
            tot = g_orig + b_orig
            if tot > 0: def_parts.append(f"{p}[{tot:.2f}]")
        else:
            if g_orig > 0: def_parts.append(f"Good {p}[{g_orig:.2f}]")
            if b_orig > 0: def_parts.append(f"Bad {p}[{b_orig:.2f}]")
        def_curr_str = ", ".join(def_parts)
        
        rows.append([
            p, f"{L:.2f}", sign, nak, pada, f"{ld}/{sl}", 
            f"{dig_bala}%" if dig_bala is not None else '', f"{sthana}%", 
            status, f"{vol:.2f}", def_curr_str, currency_str, debt_str
        ])
        
    df_planets = pd.DataFrame(rows, columns=['Planet','Deg','Sign','Nakshatra','Pada','Ld/SL','Dig Bala (%)','Sthana Bala (%)','Status','Volume', 'Default Currencies', 'Currency [Phase 1]', 'Debt [Phase 1]'])
    
    # ... (Rest of formatting for Rasi/Nav/Dasa remains same)
    
    return {
        'name': name, 'df_planets': df_planets, 'df_rasi': df_rasi, 'df_nav': df_nav,
        'df_house_status': df_house_status, 'dasa_periods_filtered': dasa_filtered,
        'lagna_sid': lagna_sid, 'nav_lagna': nav_lagna, 'lagna_sign': lagna_sign,
        'nav_lagna_sign': get_sign(nav_lagna), 'moon_rasi': get_sign(moon_lon),
        'moon_nakshatra': get_nakshatra_details(moon_lon)[0], 'moon_pada': get_nakshatra_details(moon_lon)[1],
        'selected_depth': depth_map[max_depth], 'utc_dt': utc_dt, 'max_depth': max_depth,
        'house_to_planets_rasi': house_planets_rasi, 'house_to_planets_nav': house_planets_nav
    }

# ---- South Indian plotter ----
def plot_south_indian_style(ax, house_to_planets, lagna_sign, title):
    sign_positions = {'Pisces':(0,3),'Aries':(1,3),'Taurus':(2,3),'Gemini':(3,3),
                      'Cancer':(3,2),'Leo':(3,1),'Virgo':(3,0),
                      'Libra':(2,0),'Scorpio':(1,0),'Sagittarius':(0,0),
                      'Capricorn':(0,1),'Aquarius':(0,2)}
    lagna_idx = sign_names.index(lagna_sign)
    house_for_sign = {s: ((i - lagna_idx) % 12) + 1 for i, s in enumerate(sign_names)}
    box_w, box_h, spacing, pad = 0.46, 0.46, 0.52, 0.02
    top_pad_extra = 0.020
    line_h_min, line_h_max = 0.042, 0.058
    planet_font = 2.45
    for sign,(gx,gy) in sign_positions.items():
        h = house_for_sign[sign]
        planets = sorted(house_to_planets.get(h,[]))
        x = gx*spacing + 0.22; y = (3-gy)*spacing + 0.22
        ax.add_patch(FancyBboxPatch((x,y), box_w, box_h,
                                    boxstyle="round,pad=0.004",
                                    ec="black", fc="#F5F5F5",
                                    alpha=0.92, linewidth=0.32))
        ax.text(x+pad, y+pad, sign[:3], ha='left', va='top', fontsize=2.7)
        if planets:
            avail = box_h - (pad + 0.064)
            n = len(planets)
            line_h = min(line_h_max, max(line_h_min, avail / max(1, n)))
            start_y = y + pad + 0.040 + top_pad_extra
            for i, p in enumerate(planets):
                py = start_y + i*line_h
                ax.text(x + box_w/2, py, p, ha='center', va='top', fontsize=planet_font)
    ax.set_xlim(0,3); ax.set_ylim(0,3); ax.set_aspect('equal'); ax.invert_yaxis()
    ax.set_title(title, fontsize=3.6, fontweight='normal')
    ax.axis('off')

# ---- Streamlit UI ----
st.set_page_config(page_title="Sivapathy Horoscope", layout="wide")
st.markdown("""
<style>
    .stApp { background-color: white; color: #125336; }
    .stTextInput > div > div > input,
    .stSelectbox > div > div > select,
    .stNumberInput > div > div > input {
        background-color: white; color: #125336; border: 1px solid #125336;
    }
    .stButton > button { background-color: #125336; color: white; border: none; padding: 0.5rem 2rem; font-size: 1.1rem; font-weight: 600; }
    .stButton > button:hover { background-color: #0a3d22; box-shadow: 0 4px 6px rgba(0,0,0,0.1); }
    h1, h2, h3 { color: #125336 !important; }
    .summary-box { background-color: #f0f7f4; padding: 1.2rem; border-radius: 10px; border: 2px solid #125336; margin: 1rem 0; }
    .summary-item { font-size: 1.05rem; margin: 0.35rem 0; color: #125336; }
</style>
""", unsafe_allow_html=True)

st.title("Sivapathy Astrology Data Generator")

if 'chart_data' not in st.session_state: st.session_state.chart_data = None
if 'search_results' not in st.session_state: st.session_state.search_results = []

@st.cache_resource
def get_geolocator():
    geolocator = Nominatim(user_agent="vedic_astro_app")
    return RateLimiter(geolocator.geocode, min_delay_seconds=1)

geocode = get_geolocator()
_tf = TimezoneFinder()

def tz_for_latlon(lat: float, lon: float):
    tzname = _tf.timezone_at(lng=lon, lat=lat)
    if not tzname: return pytz.UTC
    return pytz.timezone(tzname)

_DEPTH_NAME_TO_INT = {'Dasa':1, 'Bhukti':2, 'Anthara':3, 'Sukshma':4, 'Prana':5, 'Sub-Prana':6}

def find_active_path_to_depth(periods, when_utc, target_depth, cur_depth=1):
    for lord, start, end, subs in periods:
        if start <= when_utc < end:
            if cur_depth == target_depth or not subs:
                return [(lord, start, end)]
            sub_path = find_active_path_to_depth(subs, when_utc, target_depth, cur_depth+1)
            return [(lord, start, end)] + (sub_path or [])
    return None

def collect_periods_at_depth(periods, target_depth, cur_depth=1, acc=None):
    if acc is None: acc = []
    for lord, start, end, subs in periods:
        if cur_depth == target_depth or not subs:
            acc.append((lord, start, end))
        else:
            collect_periods_at_depth(subs, target_depth, cur_depth+1, acc)
    return acc

# =========================
# Birth Details
# =========================
st.subheader("Birth Details")
name = st.text_input("Name", placeholder="Enter full name")
c1, c2, c3 = st.columns(3)
with c1:
    birth_date = st.date_input("Birth Date", value=datetime.now().date(),
                               min_value=datetime(1900,1,1).date(), max_value=datetime.now().date())
with c2:
    birth_time = st.text_input("Birth Time (HH:MM in 24-hour format)", placeholder="14:30")
with c3:
    tz_offset = st.number_input("Timezone offset at birth (hrs)", value=5.5, step=0.5)

use_custom_coords = st.checkbox("Custom birth latitude and longitude?")
if use_custom_coords:
    clat, clon = st.columns(2)
    with clat: lat = st.number_input("Birth Latitude", value=13.08, format="%.4f")
    with clon: lon = st.number_input("Birth Longitude", value=80.27, format="%.4f")
else:
    birth_city_query = st.text_input("Birth City", placeholder="Start typing birth city name...", key="birth_city_input")
    if birth_city_query and len(birth_city_query) >= 2:
        try:
            locations = geocode(birth_city_query, exactly_one=False, limit=5)
            st.session_state.search_results = [{'display': loc.address, 'lat': loc.latitude, 'lon': loc.longitude, 'address': loc.address} for loc in (locations or [])]
        except: st.session_state.search_results = []
    else: st.session_state.search_results = []

    if st.session_state.search_results:
        opts = [r['display'] for r in st.session_state.search_results]
        sel = st.selectbox("Select birth location", options=opts)
        i = opts.index(sel)
        lat = st.session_state.search_results[i]['lat']; lon = st.session_state.search_results[i]['lon']
    else:
        city_key = (birth_city_query or "").title()
        if city_key in cities_fallback:
            lat = cities_fallback[city_key]['lat']; lon = cities_fallback[city_key]['lon']
        else: lat, lon = 13.08, 80.27

max_depth_options = {1:'Dasa only',2:'Dasa + Bhukti',3:'Dasa + Bhukti + Anthara',4:'Dasa + Bhukti + Anthara + Sukshma',5:'Dasa + Bhukti + Anthara + Sukshma + Prana',6:'Dasa + Bhukti + Anthara + Sukshma + Prana + Sub-Prana'}
selected_depth_str = st.selectbox("Generate up to (depth)", list(max_depth_options.values()), index=2)
max_depth = [k for k,v in max_depth_options.items() if v == selected_depth_str][0]

if st.button("Generate Chart", use_container_width=True):
    if not name or not birth_time: st.error("Please enter Name and Birth Time.")
    else:
        try:
            with st.spinner("Calculating chart..."):
                st.session_state.chart_data = compute_chart(name, birth_date, birth_time, lat, lon, tz_offset, max_depth)
            st.rerun()
        except Exception as e: st.error(f"Error: {e}")

def show_png(fig):
    fig.tight_layout(pad=0.10)
    st.pyplot(fig, use_container_width=False, dpi=300)

# =========================
# Outputs
# =========================
if st.session_state.chart_data:
    cd = st.session_state.chart_data
    st.markdown("---")
    st.markdown(f"""
    <div class="summary-box">
        <h3>Chart Summary</h3>
        <div class="summary-item"><strong>Name:</strong> {cd['name']}</div>
        <div class="summary-item"><strong>Lagna:</strong> {cd['lagna_sign']} ({cd['lagna_sid']:.2f}°)</div>
        <div class="summary-item"><strong>Rasi (Moon Sign):</strong> {cd['moon_rasi']}</div>
        <div class="summary-item"><strong>Nakshatra:</strong> {cd['moon_nakshatra']} (Pada {cd['moon_pada']})</div>
    </div>
    """, unsafe_allow_html=True)

    st.subheader("Planetary Positions")
    st.dataframe(cd['df_planets'], hide_index=True, use_container_width=True)

    st.subheader("Rasi (D1) & Navamsa (D9) — South Indian")
    col1, col2 = st.columns(2, gap="small")
    size = (1.8, 1.8)
    fig1, ax1 = plt.subplots(figsize=size)
    plot_south_indian_style(ax1, cd['house_to_planets_rasi'], cd['lagna_sign'], 'Rasi Chart (South Indian)')
    show_png(fig1)
    fig2, ax2 = plt.subplots(figsize=size)
    plot_south_indian_style(ax2, cd['house_to_planets_nav'], cd['nav_lagna_sign'], 'Navamsa Chart (South Indian)')
    show_png(fig2)

    st.subheader("House Analysis")
    st.dataframe(cd['df_house_status'], hide_index=True, use_container_width=True)

    st.subheader(f"Vimshottari Dasa ({cd['selected_depth']})")
    dasa_rows = [{'Planet': lord, 'Start': s.strftime('%Y-%m-%d'), 'End': e.strftime('%Y-%m-%d'), 'Duration': duration_str(e-s,'dasa')} for lord, s, e, _ in cd['dasa_periods_filtered']]
    st.dataframe(pd.DataFrame(dasa_rows), hide_index=True, use_container_width=True)

    # Dasa Drill-down
    dp = cd['dasa_periods_filtered']
    if cd['max_depth'] >= 2:
        with st.expander("View Sub-periods", expanded=False):
            d_opt = [f"{p[0]} ({p[1].strftime('%Y-%m-%d')} - {p[2].strftime('%Y-%m-%d')})" for p in dp]
            sel = st.selectbox("Select Dasa:", d_opt)
            bhuktis = dp[d_opt.index(sel)][3]
            st.dataframe(pd.DataFrame([{'Planet': l, 'Start': s.strftime('%Y-%m-%d'), 'End': e.strftime('%Y-%m-%d'), 'Duration': duration_str(e-s,'bhukti')} for l,s,e,_ in bhuktis]), hide_index=True, use_container_width=True)

    # Current Micro-Periods
    st.subheader("Current City → Live Micro-Periods")
    current_city_query = st.text_input("Enter your CURRENT city", placeholder="e.g., Chennai", key="current_city_input")
    depth_choice = st.selectbox("Depth to inspect", ["Sukshma", "Prana", "Sub-Prana"])
    
    if st.button("Show current micro-periods", use_container_width=True):
        if current_city_query:
            try:
                cur_locs = geocode(current_city_query, exactly_one=False, limit=1)
                if cur_locs:
                    cur = cur_locs[0]; tz = tz_for_latlon(cur.latitude, cur.longitude)
                    now_local = datetime.now(tz); now_utc_naive = now_local.astimezone(pytz.UTC).replace(tzinfo=None)
                    active_path = find_active_path_to_depth(dp, now_utc_naive, _DEPTH_NAME_TO_INT[depth_choice])
                    flat_at_depth = collect_periods_at_depth(dp, _DEPTH_NAME_TO_INT[depth_choice])
                    
                    st.success(f"Time zone: {tz.zone} • Local now: {now_local.strftime('%Y-%m-%d %H:%M')}")
                    if active_path:
                        tbl = []
                        idx_found = -1
                        for i, (lord, s, e) in enumerate(flat_at_depth):
                            if s <= now_utc_naive < e:
                                idx_found = i
                                break
                        if idx_found != -1:
                            for l,st_t,en_t in flat_at_depth[idx_found : idx_found+6]:
                                tbl.append({"Lord": l, "Start (local)": st_t.replace(tzinfo=pytz.UTC).astimezone(tz).strftime('%Y-%m-%d %H:%M'), "End (local)": en_t.replace(tzinfo=pytz.UTC).astimezone(tz).strftime('%Y-%m-%d %H:%M'), "Duration": duration_str(en_t-st_t, depth_choice.lower())})
                        st.dataframe(pd.DataFrame(tbl), hide_index=True, use_container_width=True)
            except Exception as e: st.error(f"Error: {e}")

else: st.info("Enter birth details above and click 'Generate Chart' to begin")

st.markdown("---")
st.caption("Sivapathy Astrology Data Generator")
