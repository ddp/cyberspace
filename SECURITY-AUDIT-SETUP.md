# macOS Security Auditing Setup

**Date**: 2026-01-03
**System**: om.eludom.net (macOS)
**Log Server**: moria.eludom.net (Synology NAS with syslog-ng)

## Overview

Configured centralized security logging from macOS to Synology NAS using syslog protocol. All authentication, authorization, and critical security events are now forwarded to moria for centralized storage and analysis.

## Architecture

```
om.eludom.net (Mac)
  └─> syslogd forwards to
      └─> moria.eludom.net:514 (syslog-ng)
          └─> /var/log/mac_security/om.eludom.net_YYYYMMDD.log
```

## Configuration Files

### Mac (om.eludom.net)

**File**: `/etc/syslog.conf`
```
# Remote logging to moria.eludom.net
# Forward authentication and security events
auth.*                                          @moria.eludom.net:514
authpriv.*                                      @moria.eludom.net:514
security.*                                      @moria.eludom.net:514
*.alert                                         @moria.eludom.net:514
*.crit                                          @moria.eludom.net:514
*.emerg                                         @moria.eludom.net:514
```

**Backup**: `/etc/syslog.conf.backup.20260103`

### Synology (moria.eludom.net)

**File**: `/usr/local/etc/syslog-ng/patterndb.d/remote-mac.conf`

**Log Directory**: `/var/log/mac_security/`
**Log Format**: `${HOST}_${YEAR}${MONTH}${DAY}.log`
**Permissions**: `system:log`, mode 0640

**Listening Ports**:
- UDP 514
- TCP 514

## Events Being Logged

1. **Authentication** (`auth.*`)
   - SSH logins
   - Screen unlock
   - Login window events
   - Failed login attempts

2. **Privileged Authentication** (`authpriv.*`)
   - sudo commands
   - su commands
   - Privilege escalation events

3. **Security Events** (`security.*`)
   - Security framework events
   - TCC (Transparency, Consent, and Control) events
   - Keychain access

4. **Critical Alerts** (`*.alert`, `*.crit`, `*.emerg`)
   - System emergencies
   - Critical errors
   - Alert-level events from all facilities

## Monitoring Commands

### On moria.eludom.net

View today's logs:
```bash
sudo tail -f /var/log/mac_security/om.eludom.net_$(date +%Y%m%d).log
```

Search for sudo events:
```bash
sudo grep -i sudo /var/log/mac_security/om.eludom.net_*.log
```

Search for failed logins:
```bash
sudo grep -i "failed" /var/log/mac_security/om.eludom.net_*.log
```

View all Mac security logs:
```bash
sudo ls -lh /var/log/mac_security/
sudo tail -100 /var/log/mac_security/om.eludom.net_*.log
```

### On om.eludom.net (Mac)

Generate test events:
```bash
/tmp/security-event-generator.sh
```

Test connectivity:
```bash
nc -zv moria.eludom.net 514
```

Check syslog is running:
```bash
ps aux | grep syslogd | grep -v grep
```

Restart syslogd:
```bash
sudo killall -HUP syslogd
```

## Log Retention

Logs are stored daily with date-stamped filenames. To configure retention:

1. Create a log rotation policy on moria
2. Use Synology Log Center for automated rotation
3. Or create a cron job to clean old logs

Example retention script:
```bash
# Delete logs older than 90 days
find /var/log/mac_security/ -name "*.log" -mtime +90 -delete
```

## Modern Alternatives

Note: macOS audit(4) subsystem is deprecated. For production use, consider:

1. **Unified Logging** (`log stream`)
   ```bash
   log stream --predicate 'eventType == activityCreateEvent' \
     --level info | nc moria.eludom.net 514
   ```

2. **EndpointSecurity Framework**
   - Requires system extension
   - Real-time security event monitoring
   - Used by commercial EDR solutions

3. **Commercial Solutions**
   - CrowdStrike Falcon
   - SentinelOne
   - Jamf Protect

## Testing

Test events were generated on 2026-01-03 including:
- SSH connection events
- Sudo command execution
- Failed login attempts
- Security warnings
- Kernel alerts

Check `/var/log/mac_security/` on moria for these test events.

## Troubleshooting

**No logs appearing on moria:**
1. Check syslogd is running: `ps aux | grep syslogd`
2. Restart syslogd: `sudo killall -HUP syslogd`
3. Test connectivity: `nc -zv moria.eludom.net 514`
4. Check moria syslog-ng: `ssh moria.eludom.net "ps aux | grep syslog-ng"`

**Permission issues on moria:**
```bash
sudo chown system:log /var/log/mac_security/
sudo chmod 750 /var/log/mac_security/
```

**Restart syslog-ng on moria:**
```bash
sudo killall -HUP syslog-ng
```

## Security Considerations

1. **Unencrypted Transport**: Logs sent over UDP/TCP port 514 are unencrypted
   - Use VPN or private network
   - Or configure TLS syslog (port 6514)

2. **Log Integrity**: No message authentication
   - Consider syslog-ng with TLS and certificates

3. **Network Dependency**: Logging fails if moria is unavailable
   - Local logs still written to /var/log/

4. **Access Control**: Logs contain sensitive information
   - Restrict access to /var/log/mac_security/
   - Review log file permissions regularly

## References

- macOS syslog.conf man page: `man syslog.conf`
- syslog-ng documentation: https://www.syslog-ng.com/
- RFC 5424: The Syslog Protocol
- RFC 3164: BSD syslog Protocol
