#ifndef SIMPLE_STRINGS_H
#define SIMPLE_STRINGS_H 1

int		string_compare (char *s, char *t);
int		stringn_compare (char *s, char *t, int n);
int		string_prefix (char *string, char *prefix);
char	*string_match (char *string, char *substring);
void	lowerstring (char *string);
void	uppercase_string (char *string);
long	capitalize (char *string);
void	capitalize_string(char *string);

extern char *uppercase, *lowercase;
#define DOWNCASE(x) (lowercase[x])
#define UPCASE(x) (uppercase[x])

#if !MEMORY_CHECK
char *dup_string (char *string);
#endif


/* The do-while (0) below is a slimy trick taught to me by Martin Minow. 
// This allows you to use the macro anyplace that an expression can be
// used, like a non-compound consequence of an if.	jdcc
*/

#define restype_to_chars(restype, chars)	\
	do { unsigned long rtype = restype;		\
		 char *rt = (char *) &rtype,		\
			  *ch = chars;					\
		 *ch++ = (rtype >> 24) & 0xff;		\
		 *ch++ = (rtype >> 16) & 0xff;		\
		 *ch++ = (rtype >> 8) & 0xff;		\
		 *ch++ = (rtype) & 0xff;			\
	    } while (0)


#define chars_to_restype(chars, restype)	\
	do { unsigned long rtype;				\
		 unsigned char *rt = (char *) &rtype, \
			  *ch = chars;					\
		 rtype = ch[0];						\
		 rtype |= ch[1] << 8;				\
		 rtype |= ch[2] << 16;				\
		 rtype |= ch[3] << 12;				\
		 restype = rtype;					\
	    } while (0)



#endif
