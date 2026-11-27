# Family dashboard

A wall or kitchen-screen dashboard built for a weak kiosk PC, plus a phone app that runs it. The kiosk
shows the clock and greeting, weather, this week's calendar (Monday to Sunday), a family message
board, a Party panel for chores-as-an-RPG, an optional photo panel from an Immich album, and a
rotating wallpaper (your own upload, or NASA / Bing / Wikimedia Commons / Unsplash picture of the day).

The server does all the fetching and caching, so the kiosk only renders one page. One Python file
(standard library plus two calendar packages, SQLite for the app's data), two HTML pages, about 30 MB
of RAM.

## The family app (`/app`)

The kiosk has no touch, so everything is done from phones at `http://<your-server>:8096/app` (add it
to the home screen). Five tabs:

- **Quests:** chores as a role-playing game for the whole family. Everyone has a character with a
  class, level, XP, gold and six D&D-style ability scores that grow with the kind of quests they do.
  Parents make quests (daily, some weekdays or once; for certain people or on a bounty board), approve
  them, award bonuses and stock a reward shop. Optional modules, each with its own switch:
  - **Goals:** long quests with a progress bar. Kids propose their own; parents set the reward.
  - **Habits:** small daily things tapped off on the phone, shown as a week of dots.
  - **Fitness:** log active minutes for STR XP, with a weekly goal and a bonus for reaching it.
  No penalties by design: nothing is ever taken away for a miss, and there are no streaks to break.
- **Lists:** shared lists made in the app, alongside lists pushed from an iPhone Shortcut.
- **Remote:** put a detail page on the kitchen screen for a few minutes: the full weather, a day, a
  month of the calendar, or someone's character sheet. A TV remote's arrows and OK do the same on a
  Google TV running the page in a kiosk browser.
- **Messages:** the message board (also fed by email or SMS if you set that up).
- **Settings:** calendar, weather, wallpaper, photos, colors and the family list.

Profile pictures are set on each character sheet; the phone crops and shrinks them before upload.

## Install (Docker Compose)

1. Copy `family.py`, `index.html`, `app.html`, the `app-icons/` folder and `compose.yaml` to the
   folder the compose file mounts (`/mnt/user/appdata/family` by default; change the volume for other
   hosts). The container runs as `99:100`, so `chown -R 99:100` that folder or change `user:`.
2. Copy `env.example` to `.env` and set at least `TZ` and a long random `LIST_TOKEN`.
3. `docker compose up -d`. The first start installs two small calendar libraries into `vendor/`.
4. Open `http://<your-server>:8096` on the kiosk and `http://<your-server>:8096/app` on a phone. Set
   a **parent PIN** first (Settings > Parent PIN), then the calendar, weather location and the family
   list. (`/settings` from older versions redirects to the app.)

## Lists from an iPhone Shortcut

The Shortcut sends `POST /api/lists` with JSON `{"list": "Groceries", "items": "milk\neggs"}` and the
header `Authorization: Bearer <LIST_TOKEN>`. Settings in the app shows the exact header value.

## Security

There are no user accounts; keep it on your LAN or VPN. With a parent PIN set, settings, making
quests and rewards, approvals and deleting lists need it; a phone unlocks once and stays signed in
(the token is stored hashed). The PIN is stored as a PBKDF2 hash with a lockout after five wrong
tries. Calendar addresses, API keys and the PIN live server-side in `data/private.json` (mode 600) and
are never sent back to the browser.

## Files the server writes

`data/` (settings, private keys, `family.db` with lists, quests and sign-ins, profile pictures, cached
wallpapers) and `vendor/` are per-install and kept out of git.
