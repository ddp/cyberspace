@echo off

"%CHICKEN_CSI%" -e "(if (symbol? #:foo) (exit 0) (exit 1))"

IF errorlevel 1 (
    copy srfi-18.types.in srfi-18.types
    echo ^(srfi-18#thread-wait-for-i/o! ^(#^(procedure #:clean #:enforce^) srfi-18#thread-wait-for-i/o! ^(fixnum #!optional keyword^) undefined^)^) >> srfi-18.types
) ELSE (
    copy srfi-18.types.in srfi-18.types
    echo ^(srfi-18#thread-wait-for-i/o! ^(#^(procedure #:clean #:enforce^) srfi-18#thread-wait-for-i/o! ^(fixnum #!optional symbol^) undefined^)^) >> srfi-18.types
)

"%CHICKEN_CSC%" -C "%CFLAGS%" -L "%LDFLAGS%" %*

