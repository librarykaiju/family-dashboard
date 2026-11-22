# Family dashboard

A wall or kitchen-screen dashboard built for a weak kiosk PC: clock and greeting, weather, this
week's calendar (Monday to Sunday), to-do lists pushed from an iPhone Shortcut, an optional photo
panel from an Immich album, and a rotating wallpaper (your own upload, or NASA / Bing / Wikimedia
Commons / Unsplash picture of the day).

The server does all the fetching and caching, so the kiosk only renders one page. One Python file
(standard library plus two calendar packages) and two HTML files, about 30 MB of RAM.

## Install (Docker Compose)

1. Copy `family.py`, `index.html`, `settings.html` and `compose.yaml` to the folder the compose file
   mounts (`/mnt/user/appdata/family` by default; change the volume for other hosts). The container
   runs as `99:100`, so `chown -R 99:100` that folder or change `user:`.
2. Copy `env.example` to `.env` and set at least `TZ` and a long random `LIST_TOKEN`.
3. `docker compose up -d`. The first start installs two small calendar libraries into `vendor/`.
4. Open `http://<your-server>:8096` on the kiosk, and `http://<your-server>:8096/settings` from a
   phone or PC to set the calendar, weather location, wallpaper, photo album and colors.

## Lists from an iPhone Shortcut

The Shortcut sends `POST /api/lists` with JSON `{"list": "Groceries", "items": "milk\neggs"}` and the
header `Authorization: Bearer <LIST_TOKEN>`. The settings page shows the exact address and header value.

## Security

The dashboard and its settings page have no login, and the settings page shows the list token. Keep it
on your LAN or VPN. Calendar addresses and API keys pasted on the settings page are stored server-side
in `data/private.json` (mode 600) and never sent back to the browser.

## Files the server writes

`data/` (lists, settings, private keys, cached wallpapers) and `vendor/` are per-install and kept out of git.
