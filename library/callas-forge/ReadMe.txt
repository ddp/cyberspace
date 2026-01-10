Legal stuff:

The programs here are copyright 2000-2004 by Jon Callas. Email to <jon@callas.org>.

You have license to adapt or use this in your software provided that you put in some reasonable place a credit that you are using Jon Callas's Multi-Lingual Password Generator.

I am not picky about where the reasonable place is. If it's software with an about box, that's a reasonable place. If you ship a manual, the place in that where you list everyone's trademarks and so on is fine. If it's on a web site, you can find some appropriate place, as well.

Please be reasonable. I believe that open source should be open. I'm not a fan of the GPL and other restrictive licenses. Don't make me regret my stance. Thanks.

Obviously, since I am not asking much, I am not giving much in return. No warranty is expressed or implied. I don't guarantee that this code compiles. I don't claim that it won't eat your disk. Heck, it could cause global warming and give your boss a big sloppy kiss and embarrass you to death. You've been warned.

Should you find a bug, fix something, make it better, I appreciate being told. You are not obligated. Likewise, I am not obligated to do anything more for you than hand this to you. Send mail to <jon@callas.org>

Here's what is in here:

* My Lisp-Like-Stuff package. This is a subsystem for S-expressions (even SPKI-sytax ones) that also has string-handling and other things in it. I use it for the string and list handling in many of my programs. Documentation is in Lisp-Like-Stuff.c. It consists of the files:
	Allocate.h
	Atom-Reader.c
	Lisp-Like-Stuff.c, .h
	Simple-Strings.c, .h
	Tables.c, .h
	
	
	
* The ForgeWord program files:
	ForgeWord.c
	ForgeWord.h
	FWordDice.v
	FWordDice.h
	FWordMain.c
	
	
* Various language dictionaries and compiled databases.


There is also a Project Builder project here, as well as a straight Unix Makefile. Typing 'make' should make it. Note that I run on Mac OS X.

It compiles into the program "fword".

