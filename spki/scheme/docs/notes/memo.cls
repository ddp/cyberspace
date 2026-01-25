% memo.cls - LaTeX document class for Cyberspace Memos
% Inspired by RFC formatting with modern typesetting
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{memo}[2026/01/22 Cyberspace Memo Document Class]

% Base on article
\LoadClass[11pt,a4paper]{article}

% Required packages
\RequirePackage{fontspec}
\RequirePackage{geometry}
\RequirePackage{fancyhdr}
\RequirePackage{titlesec}
\RequirePackage{enumitem}
\RequirePackage{listings}
\RequirePackage{xcolor}
\RequirePackage{hyperref}
\RequirePackage{fancyvrb}

% Page geometry - generous margins like RFCs
\geometry{
  top=1in,
  bottom=1in,
  left=1in,
  right=1in
}

% Fonts - use macOS system fonts
\setmainfont{Times New Roman}
\setmonofont{Menlo}[Scale=0.9]

% Colors
\definecolor{codeblue}{HTML}{0066cc}
\definecolor{codegray}{HTML}{666666}
\definecolor{codegreen}{HTML}{228B22}
\definecolor{codebg}{HTML}{f5f5f5}
\definecolor{linkblue}{HTML}{0000cc}

% Hyperlinks
\hypersetup{
  colorlinks=true,
  linkcolor=linkblue,
  urlcolor=linkblue,
  citecolor=linkblue
}

% Section formatting - simple, clean
\titleformat{\section}
  {\normalfont\Large\bfseries}
  {\thesection.}{0.5em}{}
\titleformat{\subsection}
  {\normalfont\large\bfseries}
  {\thesubsection}{0.5em}{}
\titleformat{\subsubsection}
  {\normalfont\normalsize\bfseries}
  {\thesubsubsection}{0.5em}{}

% No section numbering by default
\setcounter{secnumdepth}{0}

% Code listings
\lstset{
  basicstyle=\ttfamily\small,
  backgroundcolor=\color{codebg},
  frame=single,
  framerule=0.5pt,
  rulecolor=\color{codegray},
  breaklines=true,
  breakatwhitespace=true,
  postbreak=\mbox{\textcolor{red}{$\hookrightarrow$}\space},
  tabsize=2,
  showstringspaces=false,
  columns=flexible,
  keepspaces=true,
  xleftmargin=0.5em,
  xrightmargin=0.5em,
  aboveskip=1em,
  belowskip=1em
}

% Scheme language definition
\lstdefinelanguage{Scheme}{
  morekeywords={define,lambda,let,let*,letrec,if,cond,else,case,and,or,
    begin,do,delay,force,quote,quasiquote,unquote,set!,
    define-syntax,syntax-rules,import,export,library,
    define-record-type,match,when,unless},
  sensitive=true,
  morecomment=[l]{;},
  morecomment=[s]{\#|}{|\#},
  morestring=[b]",
  keywordstyle=\color{codeblue}\bfseries,
  commentstyle=\color{codegreen}\itshape,
  stringstyle=\color{codegray}
}

% Bash language
\lstdefinelanguage{Bash}{
  morekeywords={if,then,else,fi,for,while,do,done,case,esac,function,
    return,exit,export,source,echo,cd,ls,rm,mkdir,cp,mv,cat,grep,
    sed,awk,git,make},
  sensitive=true,
  morecomment=[l]{\#},
  morestring=[b]",
  morestring=[b]',
  keywordstyle=\color{codeblue}\bfseries,
  commentstyle=\color{codegreen}\itshape,
  stringstyle=\color{codegray}
}

% Markdown language (minimal - for code blocks showing markdown)
\lstdefinelanguage{markdown}{
  morekeywords={},
  sensitive=false,
  morecomment=[l]{},
  morestring=[b]",
  keywordstyle=\color{codeblue}\bfseries,
  stringstyle=\color{codegray}
}

% TLA+ language
\lstdefinelanguage{tla}{
  morekeywords={VARIABLES,CONSTANTS,ASSUME,MODULE,EXTENDS,INSTANCE,
    LOCAL,THEOREM,PROOF,BY,OBVIOUS,QED,HAVE,TAKE,WITNESS,PICK,
    SUFFICES,NEW,CONSTANT,VARIABLE,STATE,ACTION,TEMPORAL,
    IF,THEN,ELSE,CASE,OTHER,LET,IN,EXCEPT,UNCHANGED,ENABLED,
    TRUE,FALSE,UNION,SUBSET,DOMAIN},
  sensitive=true,
  morecomment=[s]{(*}{*)},
  morestring=[b]",
  keywordstyle=\color{codeblue}\bfseries,
  commentstyle=\color{codegreen}\itshape,
  stringstyle=\color{codegray}
}

% Alias lowercase 'scheme' to 'Scheme'
\lstalias{scheme}{Scheme}

% Box diagram environment - simple framed verbatim
\DefineVerbatimEnvironment{diagram}{Verbatim}{frame=single,fontsize=\small,xleftmargin=1em,xrightmargin=1em}

% Memo metadata
\newcommand{\memonumber}[1]{\def\@memonumber{#1}}
\newcommand{\memotitle}[1]{\def\@memotitle{#1}}
\newcommand{\memodate}[1]{\def\@memodate{#1}}
\newcommand{\memoauthor}[2]{\def\@memoauthorname{#1}\def\@memoauthoremail{#2}}
\newcommand{\memoabstract}[1]{\def\@memoabstract{#1}}

% Memo title block
\renewcommand{\maketitle}{%
  \begin{center}
    {\Large\bfseries Memo \@memonumber: \@memotitle}\\[1em]
    {\normalsize Date: \@memodate}\\
    {\normalsize Author: \@memoauthorname\ $<$\@memoauthoremail$>$}
  \end{center}
  \vspace{0.5em}
  \hrule
  \vspace{1.5em}
  \ifx\@memoabstract\undefined\else
    \noindent\textbf{Abstract}\\[0.5em]
    \noindent\@memoabstract
    \vspace{1.5em}
  \fi
}

% Footer
\newcommand{\memofooter}[1]{%
  \vfill
  \hrule
  \vspace{0.5em}
  \begin{center}
    #1
  \end{center}
}

% Convenience: inline code
\newcommand{\code}[1]{\texttt{#1}}

\endinput
