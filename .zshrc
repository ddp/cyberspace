# .zshrc - translated from tcsh configuration

# Interactive shell check (zsh equivalent)
if [[ -o interactive ]]; then

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

    # Enable completion system
    autoload -Uz compinit && compinit
    
    # Terminal settings
    stty -parenb -istrip cs8
    
    # Prompt configuration
    PROMPT='%n@%m%# '
    
    # OS detection and distribution setting
    if [[ "$OSTYPE" == "darwin"* ]]; then
        export OS_DISTRO=$(uname -a | awk '{ print $4 }')
    elif [[ "$OSTYPE" == "linux"* ]]; then
        export OS_DISTRO=$(uname -a | awk '{ print $6 }')
    fi
    
    # Environment variables
    export EGG_FRECKELS=T
    
    # Homebrew configuration
    export HOMEBREW_CELLAR=/opt/homebrew/Cellar
    export HOMEBREW_PREFIX=/opt/homebrew
    export HOMEBREW_REPOSITORY=/opt/homebrew
    export HOMEBREW_NO_ENV_HINTS=T
    
    # MANPATH and INFOPATH with conditional appending
    export MANPATH="/opt/homebrew/share/man${MANPATH:+:${MANPATH}}:"
    export INFOPATH="/opt/homebrew/share/info${INFOPATH:+:${INFOPATH}}"
    
    # Java configuration
    export JAVA_HOME="/Users/ddp/Library/Caches/Coursier/arc/https/cdn.azul.com/zulu/bin/zulu21.42.19-ca-jdk21.0.7-macosx_aarch64.tar.gz/zulu21.42.19-ca-jdk21.0.7-macosx_aarch64"
    
    # PATH configuration
    path=(
        $path
        ~/bin
        /opt/homebrew/bin
        /Library/Frameworks/Python.framework/Versions/3.13/bin
        ~/src/plan9
    )
    
    # SSH hosts completion (zsh style)
    if [[ -f ~/.ssh/known_hosts ]]; then
        hosts=($(sed -e 's/^ *//' -e '/^#/d' -e 's/[, ].*//' -e '/\[/d' ~/.ssh/known_hosts | sort -u))
        zstyle ':completion:*:ssh:*' hosts $hosts
        zstyle ':completion:*:scp:*' hosts $hosts
    fi
    
    # Locale and system settings
    export BLOCKSIZE=K
    export LANG=en_US.ISO_8859-1
    export LC_ALL=en_US.UTF-8
    export LC_CTYPE=en_US.UTF-8
    export TZ=:/etc/localtime
    
    # Emacs configuration
    if [[ -n "$TMPDIR" ]]; then
        export EMACS_PATH=/Applications/Emacs.app/Contents/MacOS
        alias emacs="$EMACS_PATH/Emacs -nw"
        alias emacsclient="$EMACS_PATH/bin/emacsclient -n -s $TMPDIR/emacs501/editor"
        alias ec="$EMACS_PATH/bin/emacsclient -n -s $TMPDIR/emacs501/editor"
    fi
    export EDITOR=emacs
    export TOOLCHAINS=swift
    
    # Useful zsh shortcuts
    alias ..='cd ..'
    alias ...='cd ../..'
    alias ....='cd ../../..'
    alias sudo='sudo '              # trailing space enables alias expansion
    alias please='sudo'
    alias -g G='| grep'             # global alias: cmd G pattern
    alias -g L='| less'             # global alias: cmd L

    alias aliases="alias | sort"
    alias csi="rlwrap csi"
    alias epoch="date +%s"
    alias fen="~/bin/forge-word"
    alias gstat="git status -uno"   # ignore untracked files
    alias grep="grep -i"            # ignore case
    alias hd="xxd -g 4"
    alias hst="~/bin/hst.pl"
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
    alias mayfair="rlwrap ~/src/dvcs/BIN/microvax3900"
    alias netscan="nmap -sT -v 192.168.0.0/24"
    alias pdp10="rlwrap ~/src/dvcs/BIN/pdp10"
    alias pids="ps -eo pid,comm"
    alias portmap="nmap -sT -Pn -v 192.168.0.0/24"
    alias portscan="nmap -sT -Pn -v 192.168.0.0/24"
    alias purge="~/bin/purge"
    alias sbcl="rlwrap /usr/local/bin/sbcl --noinform"
    alias ssh="ssh -X -K"       # X11 forwarding, delegate Kerberos
    alias stash="ssh-add --apple-use-keychain"
    alias top="top -r"
    alias weather="curl http://wttr.in/94903"
    
    # Host-specific DISPLAY setting
    case "$HOST" in
        om|ombra|fedora)
            export DISPLAY=192.168.1.33:0.0
            ;;
    esac
    
    # SSH key management - platform specific
    if [[ "$(uname -s)" == "Darwin" ]]; then
        # macOS - use keychain (UseKeychain yes in ~/.ssh/config)
        # No agent startup needed
    else
        # Linux/FreeBSD - use ssh-agent with persistence
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

# opam configuration
if [[ -f '/Users/ddp/.opam/opam-init/init.zsh' ]]; then
    source '/Users/ddp/.opam/opam-init/init.zsh' &>/dev/null
fi
