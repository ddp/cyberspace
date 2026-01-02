# .zshrc - translated from tcsh configuration

# Interactive shell check (zsh equivalent)
if [[ -o interactive ]]; then

    umask 027                      # -rwxr-x---
    
    # History configuration - enhanced for better experience
    HISTSIZE=50000                 # much larger history buffer
    SAVEHIST=50000                 # save more history to file
    HISTFILE=~/.zsh_history
    
    # Core zsh options for better usability
    setopt AUTO_LIST               # list completions on ambiguous completion
    setopt AUTO_MENU               # use menu completion after second tab
    setopt HIST_EXPAND             # expand history (equivalent to autoexpand)
    setopt COMPLETE_IN_WORD        # allow completion in middle of word
    setopt ALWAYS_TO_END           # move cursor to end after completion
    setopt AUTO_CD                 # type directory name to cd
    setopt HIST_IGNORE_DUPS        # don't record duplicate commands
    setopt HIST_REDUCE_BLANKS      # remove extra whitespace from history
    setopt EXTENDED_GLOB           # enable advanced glob patterns (**/*.ml)
    setopt SHARE_HISTORY           # share history across all zsh sessions
    setopt APPEND_HISTORY          # append to history file, don't overwrite
    setopt PUSHD_IGNORE_DUPS       # don't add duplicate directories to stack
    setopt PUSHD_SILENT            # make pushd/popd quiet
    setopt NUMERIC_GLOB_SORT       # sort numbers naturally (1,2,10 not 1,10,2)
    setopt GLOB_DOTS               # include dotfiles in glob patterns
    setopt INC_APPEND_HISTORY      # add commands to history immediately

    # interpret '#' as a comment prefix only if an interactive shell
    [[ -o interactive ]] && setopt INTERACTIVE_COMMENTS
    
    # Enable completion system
    autoload -Uz compinit && compinit
    
    # Terminal settings
    stty -parenb -istrip cs8
    
    # Prompt configuration
    PROMPT='%n@%m%# '
    
    # Environment variables
    export EGG_FRECKELS=T
    
    # OS PATH detection
    path=(
        $path
        ~/bin
        ~/src/plan9
        /Library/TeX/texbin
    )

    if [[ "$OSTYPE" == "darwin"* ]]; then
        arch="$(uname -m)"

        export HOMEBREW_NO_INSTALL_CLEANUP=1
        export HOMEBREW_NO_ENV_HINTS=1

        if [[ "$arch" == "arm64" ]]; then
            # Apple Silicon: Homebrew in /opt
            if [[ -x /opt/homebrew/bin/brew ]]; then
                eval "$(/opt/homebrew/bin/brew shellenv)"
            fi
            path=(
                $path
                $HOME/.local/bin
                /opt/homebrew/bin
                /Library/Frameworks/Python.framework/Versions/3.13/bin
            )
        else
            # x86_64: Homebrew in /usr (typically /usr/local)
            if [[ -x /usr/local/bin/brew ]]; then
                eval "$(/usr/local/bin/brew shellenv)"
            elif [[ -x /usr/bin/brew ]]; then
                eval "$(/usr/bin/brew shellenv)"
            fi
            path=(
                $path
                $HOME/.local/bin
                /usr/local/bin
                /Library/Frameworks/Python.framework/Versions/3.13/bin
            )
        fi

    elif [[ "$OSTYPE" == "linux"* ]]; then
        # echo ".zprofile on linux*"
        :
    fi

    # SSH hosts completion (zsh style)
    if [[ -f ~/.ssh/known_hosts ]]; then
        hosts=($(sed -e 's/^ *//' -e '/^#/d' -e 's/[, ].*//' -e '/\[/d' ~/.ssh/known_hosts | sort -u))
        zstyle ':completion:*:ssh:*' hosts $hosts
        zstyle ':completion:*:scp:*' hosts $hosts
    fi
    
    # Locale and system settings
    export BLOCKSIZE=K
    export LANG=en_US.UTF-8
    export LC_ALL=en_US.UTF-8
    export LC_CTYPE=en_US.UTF-8
    export TZ=:/etc/localtime
    
    # Emacs configuration
    EMACS_PATH=/Applications/Emacs.app/Contents/MacOS
    EMACS="$EMACS_PATH/Emacs"
    EMACSCLIENT="$EMACS_PATH/bin/emacsclient"

    if [[ -x "$EMACS" && -x "$EMACSCLIENT" ]]; then
        export EMACS_PATH

        # Terminal emacs convenience
        alias emacs="$EMACS -nw"

        # Fast "open in GUI if possible" helper (no-wait is fine for interactive use)
        ec() { "$EMACSCLIENT" -n -s ns -c -a "$EMACS" "$@"; }

        # Blocking variants (useful when a caller expects the editor to wait)
        ect() { "$EMACSCLIENT"      -s ns -t -a "$EMACS" "$@"; }
        ecg() { "$EMACSCLIENT"      -s ns -c -a "$EMACS" "$@"; }

        # Helper for Claude Code (hardcoded paths for when env vars aren't sourced)
        emacs-open() { /Applications/Emacs.app/Contents/MacOS/bin/emacsclient -n -s ns -c -a /Applications/Emacs.app/Contents/MacOS/Emacs "$@"; }

        # What programs like crontab(1) consult
        export EDITOR="$HOME/.local/bin/ec-ns-tty"
        export VISUAL="$HOME/.local/bin/ec-ns-gui"
    fi

    batt() {
        sysctl -n hw.acpi.battery.life 2>/dev/null | awk '{print $1 "%"}'
    }

    updateapalooza() {
        brew update && brew upgrade &&
        sudo port selfupdate &&
        opam update && opam upgrade &&
        npm update && npm upgrade
    }

    # Useful zsh shortcuts
    alias ..='cd ..'
    alias ...='cd ../..'
    alias ....='cd ../../..'
    alias sudo='sudo '              # trailing space enables alias expansion
    alias please='sudo'
    alias -g G='| grep'             # global alias: cmd G pattern
    alias -g L='| less'             # global alias: cmd L

    alias aliases="alias | sort"
    alias cc="claude --continue"
    alias chibi="rlwrap chibi-scheme"
    alias chez="rlwrap chez"
    alias chicken="rlwrap csi"
    alias cr="claude --resume"
    alias clone="stash && clone-fluffy --with-dotfiles"
    alias csi="rlwrap csi"
    alias epoch="date +%s"
    alias fen="~/bin/forge-word"
    alias gonorns="ssh we@192.168.0.161"
    alias gc="yt-dlp --merge-output-format mkv https://www.twitch.tv/djmissshelton"
    alias grab="yt-dlp --merge-output-format mkv "
    alias cb="yt-dlp --merge-output-format mkv https://chaturbate.com/"
    alias grep="grep -i"            # ignore case
    alias gstat="git status -uno"   # ignore untracked files
    alias guile="rlwrap guile"      # Keep guile if you still want it
    alias hd="xxd -g 4"
    alias hst="~/bin/hst.pl"
    alias ls="ls -h "
    alias lsacc="ls -lau"
    alias lsacl="ls -lae"
    alias lsattr="ls -la@"
    alias lsctl="ls -lac"
    alias lsdot="ls -lad .*"
    alias lsenv="env | sort"
    alias lsflag="ls -laO"
    alias lsflags="ls -laO"
    alias lsmod="ls -lat"
    alias lsnew="ls -laU"
    alias lssym="ls -la | grep -e '->' | sort"
    alias lsuse="ls -lau"
    alias lstree="tree -h -L 2 . && echo \"Total size: \$(du -sh . | cut -f1)\""
    alias lsxattr="ls -la@"
    alias mayfair="rlwrap ~/src/dvcs/BIN/microvax3900"
    alias netscan="nmap -sT -v 192.168.0.0/24"
    alias norns="ping -c 1 192.168.0.161; ping6 -c1 norns.local"
    alias path\?="lsenv | grep PATH"
    alias pdp10="rlwrap ~/src/dvcs/BIN/pdp10"
    alias pids="ps -eo pid,comm"
    alias pip="pip3"
    alias python="python3"
    alias portmap="nmap -sT -Pn -v 192.168.0.0/24"
    alias portscan="nmap -sT -Pn -v 192.168.0.0/24"
    alias purge="~/bin/purge"
    alias scheme="rlwrap csi"   # Chicken Scheme
    alias ssh="ssh -X -K"       # X11 forwarding, delegate Kerberos
    alias stash="ssh-add --apple-use-keychain"
    alias weather="curl http://wttr.in/94903"
    
    # Host-specific DISPLAY setting
    case "$HOST" in
        om|ombra)
            export DISPLAY=192.168.1.33:0.0
            ;;
        fedora)
            export DISPLAY=:0.0
            ;;
    esac

    # SSH key management - platform specific
    if [[ "$(uname -s)" == "Darwin" ]]; then
        # macOS - use keychain (UseKeychain yes in ~/.ssh/config)
        alias stash="ssh-add --apple-use-keychain"
    else
        # Linux/FreeBSD - use ssh-agent with persistence
        alias stash="ssh-add"
        
        agent_env=~/.ssh/agent-env
        
        if [[ -f "$agent_env" ]]; then
            source "$agent_env" > /dev/null
        fi
        
        ssh-add -l &>/dev/null
        if [[ $? == 2 ]]; then
            eval $(ssh-agent)
            echo "export SSH_AUTH_SOCK=$SSH_AUTH_SOCK" > "$agent_env"
            echo "export SSH_AGENT_PID=$SSH_AGENT_PID" >> "$agent_env"
            ssh-add
        fi
    fi
fi

# MacPorts: use the real directory, not the symlink
export MANPATH="~/.local/share/man:/opt/local/share/man:$MANPATH"

# TeXLive: use the real tree instead of the two symlinks
export MANPATH="/usr/local/texlive/2025/texmf-dist/doc/man:$MANPATH"

# Common Lisp: architecture-specific (SBCL for arm64, Clozure for x86_64)
arch="$(uname -m)"
if [[ "$arch" == "arm64" ]]; then
    # Apple Silicon: use SBCL
    export PATH="$HOME/bin/sbcl/bin:$PATH"
    export SBCL_HOME="$HOME/bin/sbcl/lib/sbcl"
    alias sbcl='rlwrap sbcl --noinform'
    alias lisp='rlwrap sbcl --noinform'
else
    # x86_64: use Clozure CL
    export PATH="$HOME/bin/ccl:$PATH"
    export CCL_DEFAULT_DIRECTORY="$HOME/bin/ccl"
    alias ccl='rlwrap ccl'
    alias lisp='rlwrap ccl'
fi

# OCaml/opam if you're using it
[[ ! -r $HOME/.opam/opam-init/init.zsh ]] || source $HOME/.opam/opam-init/init.zsh > /dev/null 2> /dev/null

# LibreSSL preference
export PKG_CONFIG_PATH="/opt/homebrew/lib/pkgconfig:$PKG_CONFIG_PATH"

test -e "${HOME}/.iterm2_shell_integration.zsh" && source "${HOME}/.iterm2_shell_integration.zsh"

