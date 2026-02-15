# Cyberspace Minimal - Headless Server

**No GUI** - Perfect for servers, Docker, or lightweight systems.

## What It Is

Just the Chez Scheme server running on port 7780.
Access via any browser: `http://localhost:7780`

## Requirements

- Chez Scheme 10.0+
- That's it!

## Install Chez

**Fedora**:
```bash
sudo dnf install chez-scheme
```

**Ubuntu/Debian**:
```bash
sudo apt install chezscheme
```

**Arch**:
```bash
sudo pacman -S chez-scheme
```

**From source**:
```bash
git clone https://github.com/cisco/ChezScheme.git
cd ChezScheme && ./configure && make && sudo make install
```

## Running

### Local (Development)
```bash
./cyberspace-server
```

### Custom Port
```bash
PORT=8080 ./cyberspace-server
```

### Background (Daemon)
```bash
nohup ./cyberspace-server > cyberspace.log 2>&1 &
```

### Systemd Service
```bash
sudo cp cyberspace.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now cyberspace
```

Access: `http://localhost:7780`

## Docker

```dockerfile
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y chezscheme
COPY cyberspace-server /app/
WORKDIR /app
EXPOSE 7780
CMD ["./cyberspace-server"]
```

Build and run:
```bash
docker build -t cyberspace .
docker run -p 7780:7780 cyberspace
```

## Reverse Proxy (nginx)

```nginx
server {
    listen 80;
    server_name cyberspace.example.com;

    location / {
        proxy_pass http://127.0.0.1:7780;
        proxy_set_header Host $host;
    }
}
```

## SSH Tunneling

Access from remote machine:
```bash
ssh -L 7780:localhost:7780 user@server
```

Then open: `http://localhost:7780`

## Memory Usage

- **Server only**: ~30MB
- **With active session**: ~50MB
- **Multiple vaults**: ~100MB

## Performance

- **Startup**: <500ms
- **Request latency**: <10ms
- **Threading**: Native Chez threads

## Use Cases

✅ **Headless servers**
✅ **Raspberry Pi**
✅ **Docker containers**
✅ **WSL (Windows)**
✅ **SSH-only access**
✅ **Low-end hardware**
✅ **Multi-user setups** (with nginx reverse proxy)

## Systemd Service File

`/etc/systemd/system/cyberspace.service`:
```ini
[Unit]
Description=Cyberspace Server
After=network.target

[Service]
Type=simple
User=cyberspace
WorkingDirectory=/opt/cyberspace
ExecStart=/usr/local/bin/cyberspace-server
Restart=on-failure
RestartSec=5s

[Install]
WantedBy=multi-user.target
```

Enable and start:
```bash
sudo systemctl enable --now cyberspace
```

Check status:
```bash
sudo systemctl status cyberspace
journalctl -u cyberspace -f
```

## Security

### Firewall (Local Only)
```bash
# UFW
sudo ufw allow from 127.0.0.1 to any port 7780

# firewalld
sudo firewall-cmd --permanent --add-rich-rule='rule family="ipv4" source address="127.0.0.1" port port="7780" protocol="tcp" accept'
```

### Network Access
To allow LAN access:
```bash
# Bind to all interfaces (edit server script)
chez --libdirs . --script server.sps 7780 0.0.0.0
```

**Warning**: Only do this on trusted networks!

## Troubleshooting

**Port in use**:
```bash
lsof -i :7780  # Find what's using it
```

**Server won't start**:
```bash
chez --version  # Check Chez is installed
which chez      # Check it's in PATH
```

**Can't access from browser**:
```bash
curl http://localhost:7780  # Test locally
netstat -tlnp | grep 7780   # Check it's listening
```

---

**Minimal, fast, no GUI - perfect for servers!** 🚀
