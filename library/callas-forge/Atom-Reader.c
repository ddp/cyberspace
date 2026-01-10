/*
// Stateless Atom Reader for the Lisp-Like-Stuff.
//
// Copyright 1993, 1995, World Benders, Inc. All Rights Reserved.
// Copyright 1998, 1999, Jonathan D. Callas. All Rights Reserved.
//
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "Lisp-Like-Stuff.h"

char SymbolEnders[] =	"()[]{}\";,|";
char QuotedChars[] =	"\1\2\3\4\5\6\7\10\12\13\14\15\16\17"
						"\20\21\22\23\24\25\26\27\30\31\32\33"
						"\34\35\36\37";	              /* implicit 0! */

char Base64Chars[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                     "abcdefghijklmnopqrstuvwxyz"
                     "0123456789"
                     "+/=";
char Base64Vals[256];
int  Base64ValsInited = 0;

#define B64ENDTAG 64

#define iswhite(c)	(isspace(c) || strchr(QuotedChars, c) != NULL)
#define grab_white(s) while (*s && iswhite(*s)) s++
#define isbad(c)	(strchr(SymbolEnders, c) != NULL)

static long number_char(AtomReader *ar, char c);
static long quote_char(AtomReader *ar, char c);
static void write_pair(AtomWriter *aw);

AtomReader *create_reader(void)
{
	AtomReader *ar = ALLOCATE_CLEARED(1, AtomReader);
	
	if (ar == NULL)
		return NULL;
	
	ar->state	  = READING_WHITE;
	ar->nextState = READING_BEGIN;
	return ar;
}

void dispose_reader(AtomReader *ar)
{
	if (ar->next)
		dispose_reader(ar->next);

	if (ar->head)
		dispose_atom(ar->head);
	
	DEALLOCATE(ar);
}

Atom *reader_result(AtomReader *ar, int beGenerous)
{
	Atom *result;
	
	if (beGenerous || (NULL == ar->next))
	{
		close_reader(ar);
		result = ar->head;
		ar->head = NULL;
		dispose_reader(ar);
		return result;
	}
	else		/* This critter is n-levels deep. This is an error. */
	{
		dispose_reader(ar);
		return NULL;
	}
}


void close_reader(AtomReader *ar)
{
	if (ar->next)
		close_reader(ar->next);
	
	switch (ar->state)
	{
		case READING_END:			/* Do nothing. We're done. */
		case READING_ERROR:
			break;
		
		case READING_BEGIN:			/* Set state to done. */
			ar->state = READING_END;
			break;
		
		case READING_WHITE:			/* Terminate the next state. */
			ar->state = ar->nextState;
			close_reader(ar);
			break;
		
		case READING_PLUS:
		case READING_MINUS:
		case READING_DBREF_TOKEN:
		case READING_DOT:
		case READING_COMMA:

		case READING_INT:
		case READING_SYMBOL:
		case READING_DBREF:
			feed_char(ar, ' ');		/* force a harmless read to 
                                        terminate. */
			break;
		
		case READING_QUOTE:
			quote_char(ar, '\0');	/* close this... */
			break;

		case READING_BACKQUOTE:
			/* ?????? */
			ar->state = READING_END;
			break;
		
		case READING_PAIR:
			feed_char(ar, ')');		/* End the list...      */
			break;

		case READING_STRING:
			feed_char(ar, '\"');	/* End the string...    */
			break;
		
		case READING_BASE64:
			feed_char(ar, '|');		/* End the string...    */
			break;
		case READING_HEX:
			feed_char(ar, TOKEN_HEX);	/* End the string...*/
			break;
	}
}

Atom *read_atom(char **string)
{
	char		*s = *string;
	AtomReader	*ar = NULL;
	Atom		*a;
	
	if (NULL == s)
		return NULL;

	grab_white(s);					/* Pull off whitespace because 
                                        that's easiest. */
	if (*s == '\0')
	{
		*string = s;
		return NULL;
	}
	
	ar = read_from_string(ar, &s);

	if (ar->state != READING_END)
		close_reader(ar);
	
	*string = s;
	
	a = ar->head;
	ar->head = NULL;
	dispose_reader(ar);
	
	return a;	
}

Atom *read_atom_from_binary(char **string, long length)
{
	char		*s = *string;
	AtomReader	*ar = NULL;
	Atom		*a;
	
	if (NULL == s)
		return NULL;

	ar = read_from_binary_string(ar, &s, length);

	if (ar->state != READING_END)
		close_reader(ar);
	
	*string = s;
	
	a = ar->head;
	ar->head = NULL;
	dispose_reader(ar);
	
	return a;	
}

AtomReader *read_from_string(AtomReader *ar, char **string)
{
	char		*s = *string;

	if (ar == NULL)
	{
		ar = create_reader();
		if (ar == NULL)
			return NULL;
	}
	
	if (s == NULL)
		return ar;
	
	while (*s && ar->state != READING_END)
		feed_char(ar, *s++);
	
	*string = s;
	
	return ar;
}

AtomReader *read_from_binary_string(AtomReader *ar, 
                                    char **string, long slen)
{
	char		*s = *string;
	long		i;

	if (ar == NULL)
	{
		ar = create_reader();
		if (ar == NULL)
			return NULL;
	}
	
	if (s == NULL)
		return ar;
	
	for (i = 0; i < slen; i++)
	{
		if (ar->state == READING_END)
			break;
		feed_char(ar, *s++);
	}

	*string = s;
	
	return ar;
}

void dump_reader (AtomReader *ar)
{
	if (NULL == ar)
	{
		printf("NULL reader\n");
		return;
	}
	
	printf("reader: state = %.4s, next-state = %.4s, substate = %.4s ", 
			&ar->state, &ar->nextState, &ar->substate);
	if (ar->head)
	{
		printf("holding: ");
		print_atom(ar->head);
		if (ar->current != ar->head)
		{
			printf("pointing to: ");
			print_atom(ar->current);
		}
	}
	else
	{
		printf("holding nothing\n");
	}
	
	if (ar->next)
	{
		printf("subreader: ");
		dump_reader(ar->next);
	}
}

static long begin_char(AtomReader *ar, char c)
{
	if (c == '\0')
	{
		return READING_BEGIN;
	}
	else if (c == ' ')
	{
		ar->nextState = READING_BEGIN;
		ar->state = READING_WHITE;
		return ar->state;
	}
	else if (c == '(')
	{
		ar->head = nil_pair();
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->current = ar->head;
		ar->state = READING_PAIR;
	}
	else if (c == '\'')
	{
		ar->state = READING_QUOTE;
		ar->next = create_reader();
		if (ar->next == NULL)
		{
			ar->state = READING_ERROR;
			return ar->state;
		}
		ar->next->thisChar = ar->thisChar;
		ar->next->itsSupervisor = ar;
	}
	else if (c == '\"')
	{
		ar->head = create_string(SMALL_STRING);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->current = ar->head;
		ar->state = READING_STRING;
		return ar->state;
	}
	else if (c == '+')
	{
		ar->state = READING_PLUS;
	}
	else if (c == '-')
	{
		ar->state = READING_MINUS;
	}
	else if (c == TOKEN_DBREF)
	{
		ar->state = READING_DBREF_TOKEN;
		ar->substate = SUBSTATE_NORMAL;
	}
	else if (isdigit(c))
	{
		ar->head = create_int(0);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->state = READING_INT;
		ar->substate = SUBSTATE_NORMAL;
		ar->negative = 0;
		
		return number_char(ar, c);
	}
	else if (c == '|')
	{
		ar->head = create_base64(SMALL_STRING);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->current = ar->head;
		ar->state = READING_BASE64;
		ar->substate = 0;			/* Holds count of chars */
		ar->tempLong = 0;			/* Holds base 64 temporaries */
		return ar->state;
	}
	else if (c == TOKEN_HEX)
	{
		ar->head = create_base64(SMALL_STRING);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->current = ar->head;
		ar->state = READING_HEX;
		ar->substate = 0;			/* Holds count of chars */
		ar->tempLong = 0;			/* Holds hex temporaries */
		return ar->state;
	}
	else if (c == '{')
	{
		ar->head = create_base64(SMALL_STRING);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->current = ar->head;
		ar->state = READING_CAPSULE;
		ar->substate = 0;			/* Holds count of chars */
		ar->tempLong = 0;			/* Holds base 64 temporaries */
		return ar->state;
	}
	else if (isbad(c))
	{
		ar->head = create_string(2);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		append_atom_char(ar->head, c);
		ar->state = READING_END;
	}
	else
	{
		ar->head = create_symbol(SMALL_STRING);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->current = ar->head;
		ar->state = READING_SYMBOL;
		return _feed_char(ar, c, TRUE);	
	}
	
	return ar->state;
}

static long canonical_string_char(AtomReader *ar, char c)
{
	append_atom_char(ar->head, c);
	ar->substate--;					/* decrement the count. */
	
	if (0 == ar->substate)
	{
		ar->state = READING_END;
	}

	return ar->state;
}

static long string_char(AtomReader *ar, char c)
{
	register long tempLong;
	
	if (strchr(QuotedChars, c) != NULL)
	{
		return ar->state;
	}
	
	switch (ar->substate)
	{
		case SUBSTATE_BSLASH:
			if (isdigit(c))					/* On a digit   */
			{
				ar->substate = SUBSTATE_QDIGIT;	
				                            /* Build a number that 
                                                becomes a char. */
				ar->tempLong = 0;
				return string_char(ar, c);
			}
			else				/* Else just quote this char. */
			{
				append_atom_char(ar->head, c);
				ar->substate = SUBSTATE_NORMAL;
			}
			break;
			
		case SUBSTATE_QDIGIT:			/* In a quoted digit string */
			if ((c >= '0') && (c <= '7'))	/* add the next digit */
			{
				tempLong = ar->tempLong * 8;
				tempLong += (c - '0');
				tempLong &= 0xff;		/* Makes for 1-octet chars!!!!*/
				ar->tempLong = tempLong;
			}
			else						/* add the accumulated char */
			{
				append_atom_char(ar->head, (char) ar->tempLong);
				ar->substate = SUBSTATE_NORMAL;
				return _feed_char(ar, c, TRUE);	/* re-read the current 
                                                    char. */
			}
			break;

		default:
			if (c == '\\')
				ar->substate = SUBSTATE_BSLASH;
			else if (c == '\"')
				ar->state = READING_END;
			else
				append_atom_char(ar->head, c);
	}
	
	return ar->state;
}

static unsigned char b64_value(unsigned char c)
{
    /* return the numeric value of a b64-encoded char.*/
	if (0 == Base64ValsInited)
	{
		int i;
		unsigned char ch;
		Base64ValsInited = 1;
		/* make all illegal chars 0xff */
		memset(Base64Vals, 0xff, sizeof(Base64Vals));	
		
		for (i = 0; i < 256; i++)
		{
			ch = Base64Chars[i];
			if (ch)
				Base64Vals[ch] = i;
			else
				break;
		}
	}
	
	return Base64Vals[c];
}

static void store_base64(AtomReader *ar)
{
	unsigned char stuff[3], t;
	char *tempString = (char *) &ar->tempLong;/* Fudge a 4-char array */
	int i, count = 3;
	
	if (ar->substate != 4)					/* Not a full cell? */
	{
		if (ar->substate == 0)
			return;
		
		for (i = ar->substate; i < 4; i++)	/* Add in pad characters. */
			tempString[i] = '=';
	}
	
	t = b64_value(tempString[0]);
	if (t == B64ENDTAG)					/* The end marker value ('=') */
		count = 0;						/* Technically illegal, but 
                                           makes parsing easier. */

	stuff[0] = (t & 0x3f) << 2;			/* Move 6 bits of first byte */
	t = b64_value(tempString[1]);		/* Get next base64 char */
	stuff[0] |= ((t & 0x3f) >> 4);		/* Get low 2 bits of 1st byte */
	
	stuff[1] = (t & 0x0f) << 4;			/* Get 4 bits of second byte */
	if (t == B64ENDTAG)					/* The end marker value ('=') */
		count = 0;						/* Technically illegal, but what 
                                           the hey. */

	t = b64_value(tempString[2]);		/* Get next base64 char */
	if (t == B64ENDTAG)
		count = 1;
	stuff[1] |= (t & 0x3f) >> 2;		/* Get low 4 bits of 2nd byte */
	
	stuff[2] = (t & 0x03) << 6;			/* High 2 bits of 3rd byte */

	t = b64_value(tempString[3]);		/* Get next base64 char */
	if (t == B64ENDTAG)
		count = 2;

	stuff[2] |= (t & 0x3f);				/* Get low 6 bits of 3rd byte */
	
	for (i = 0; i < count; i++)
		append_atom_char(ar->head, stuff[i]);
	
	ar->tempLong = 0;					/* Clear temp storage */
}

static void fixup_hex(AtomReader *ar)
{
	/*
		This routine checks to see if the hex string
		had an odd number of characters in it, and if
		so, shifts the whole thing right by four bits.
	*/
	
	ar->head->llsStringLen = ar->substate;
	
	if (ar->tempLong == 1)
	{
		unsigned char hexval = 0, temp;
		unsigned int i;
		
		char *s = ar->head->llsString;
		
		for (i = 0; i < (unsigned) ar->substate; i++)
		{
			temp = s[i] & 0x0f;
			s[i] = ((s[i] >> 4) & 0x0f) | (hexval << 4);
			hexval = temp;
		}
	}
}

static long hex_char(AtomReader *ar, char c)
{
	unsigned char hexval = 0;
	
	if (isspace(c))							/* Skip passing spaces. */
		return ar->state;
	
	if (c == TOKEN_HEX)
	{
		fixup_hex(ar);
		ar->state = READING_END;
	}
	else
	{
		if (c >= '0' && c <= '9')		/* Get hex value */
			hexval = c - '0';
		else if (c >= 'A' && c <= 'F')
			hexval = 10 + (c - 'A');
		else if (c >= 'a' && c <= 'f')
			hexval = 10 + (c - 'a');
		else
		{
			/* Just ignore it presently... */
			return ar->state;
		}
		
		if (ar->tempLong == 0)	/* first char */
		{
			ar->tempLong = 1;
			hexval = hexval << 4;
			append_atom_char(ar->head, hexval); /* append another character */
			ar->substate++;
		}
		else
		{
			Atom *a = ar->head;
			
			ar->tempLong = 0;
			a->llsString[(ar->substate - 1)] |= hexval;
		}
	}
	
	return ar->state;
}

static long base64_char(AtomReader *ar, char c)
{
	char *tempString = (char *) &ar->tempLong;/* Fudge 4-char array. */
	
	if (isspace(c))							/* Skip passing spaces. */
		return ar->state;
	
	if (c == '|')
	{
		store_base64(ar);
		ar->state = READING_END;
	}
	else
	{
		if (b64_value(c) != 0xff)
		{
			tempString[ar->substate] = c;	/* Drop in a character */
			ar->substate++;					/* increment the counter */
		}
		
		if (ar->substate == 4)
		{
			store_base64(ar);
			ar->substate = 0;
		}
	}
	return ar->state;
}

static long capsule_char(AtomReader *ar, char c)
{
	char *tempString = (char *) &ar->tempLong; /* Fudge 4-char array */
	
	if (isspace(c))							/* Skip passing spaces. */
		return ar->state;
	
	if (c == '}')
	{
		Atom *temp = ar->current;
		char *s = temp->llsString;
		store_base64(ar);
		ar->current = read_atom_from_binary(&s, temp->llsStringLen);
		ar->head = ar->current;
		dispose_atom(temp);
		ar->state = READING_END;
	}
	else
	{
		if (b64_value(c) != 0xff)
		{
			tempString[ar->substate] = c;	/* Drop in a character */
			ar->substate++;					/* increment the counter */
		}
				
		if (ar->substate == 4)
		{
			store_base64(ar);
			ar->substate = 0;
		}
	}
	return ar->state;
}

static long symbol_char(AtomReader *ar, char c)
{
	if (isspace(c) || 
		(strchr(SymbolEnders, c) != NULL) || 
		(strchr(QuotedChars, c) != NULL))
	{
		ar->state = READING_END;
	}
	else
	{
		append_atom_char(ar->head, c);
	}
	return ar->state;
}

static long symbol_with_char(AtomReader *ar, char c)
{
	ar->head = create_symbol(SMALL_STRING);
	if (ar->head == NULL)
	{
		ar->state = READING_ERROR;
		return READING_ERROR;
	}
	ar->current = ar->head;
	ar->state = READING_SYMBOL;
	append_atom_char(ar->head, c);
	
	return ar->state;
}

static long number_char(AtomReader *ar, char c)
{
	if (isdigit(c))
	{
		ar->head->llsNumber *= 10;
		ar->head->llsNumber += c - '0';
	}
	else if (c == ':')
	{
		/* Oh, hell. This is a canonicalized SPKI string, one of the 
           form <number>:<n-bytes> like "4:abcd". This requires us to go 
           through a number of gyrations to re-do this as a string. Note 
           that any binary data can be in one of these critters. */
		
		ar->state = READING_CANONSTRING;
		ar->substate = ar->head->llsNumber;	/* Substate holds the number 
                                                of chars. */
											/* Note that we drop the 
                                                negative flag on the
                                                floor. */
		
		dispose_atom(ar->head);

		ar->head = create_string(SMALL_STRING);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->current = ar->head;
	}
	else
	{
		ar->state = READING_END;
		if (ar->negative)
			ar->head->llsNumber = -ar->head->llsNumber;
		if (ar->substate == SUBSTATE_DBREF)
			ar->head->tag = DBREF_ATOM;
	}
	
	return ar->state;
}

static long conjure_dbref(AtomReader *ar)
{
	ar->head = create_dbref(0);
	if (ar->head == NULL)
	{
		ar->state = READING_ERROR;
		return READING_ERROR;
	}
	ar->substate = SUBSTATE_NORMAL;
	ar->state = READING_DBREF;
	ar->substate = SUBSTATE_DBREF;

	return READING_DBREF;
}

static long dbref_token_char(AtomReader *ar, char c)
{
	long status;

	switch (ar->substate)
	{
		case SUBSTATE_NORMAL:
			if (isdigit(c))
			{
				status = conjure_dbref(ar);
				ar->negative = 0;
				
				if (status == READING_ERROR)
					return status;
				else
					return number_char(ar, c);
			}
			else if (c == '-')
			{
				ar->substate = SUBSTATE_MINUS;
			}
			else if (c == '+')
			{
				ar->substate = SUBSTATE_PLUS;
			}
			else
			{
				symbol_with_char(ar, TOKEN_DBREF);
				return _feed_char(ar, c, TRUE);
			}
			break;
		
		case SUBSTATE_MINUS:
			if (isdigit(c))
			{
				status = conjure_dbref(ar);
				ar->negative = 1;
				
				if (status == READING_ERROR)
					return status;
				else
					return number_char(ar, c);
			}
			else
			{
				symbol_with_char(ar, TOKEN_DBREF);
				append_atom_char(ar->head, '-');
				return _feed_char(ar, c, TRUE);
			}
			break;
		
		case SUBSTATE_PLUS:
			if (isdigit(c))
			{
				status = conjure_dbref(ar);
				ar->negative = 1;
				
				if (status == READING_ERROR)
					return status;
				else
					return number_char(ar, c);
			}
			else
			{
				symbol_with_char(ar, TOKEN_DBREF);
				append_atom_char(ar->head, '+');
				return _feed_char(ar, c, TRUE);
			}
			break;
		default:					/* should never happen, but cope! */
			ar->substate = SUBSTATE_NORMAL;	/* go to normal state */
			return dbref_token_char(ar, c);		/* reparse */
	}
	
	return ar->state;
}

static long minus_char(AtomReader *ar, char c)
{
	if (isdigit(c))
	{
		ar->head = create_int(0);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->substate = SUBSTATE_NORMAL;
		ar->negative = 1;
		ar->state = READING_INT;
		return number_char(ar, c);
	}
	else
	{
		symbol_with_char(ar, '-');
		return _feed_char(ar, c, TRUE);	
	}
}

static long plus_char(AtomReader *ar, char c)
{
	if (isdigit(c))
	{
		ar->head = create_int(0);
		if (ar->head == NULL)
		{
			ar->state = READING_ERROR;
			return READING_ERROR;
		}
		ar->substate = SUBSTATE_NORMAL;
		ar->negative = 0;
		ar->state = READING_INT;
		return number_char(ar, c);
	}
	else
	{
		symbol_with_char(ar, '+');
		return _feed_char(ar, c, TRUE);	
	}
}

static long pair_char(AtomReader *ar, char c)
{
	if (c == ')')
	{
		ar->state = READING_END;
	}
	else if (iswhite(c))
	{
		if (ar->state != READING_WHITE)
		{
			ar->nextState = ar->state;
			ar->state = READING_WHITE;
		}
	}
	else
	{
		if (ar->current->llsFirst != NULL)	/* Make a new thingie. */
		{
			ar->current->llsRest = nil_pair();
			ar->current = ar->current->llsRest;
		}
		
		ar->next = create_reader();
		if (ar->next == NULL)
		{
			ar->state = READING_ERROR;
			return ar->state;
		}
		ar->next->thisChar = ar->thisChar;
		ar->next->itsSupervisor = ar;

		return _feed_char(ar, c, TRUE);
	}
	
	return ar->state;
}

static long unwind(AtomReader *supervisor, char c)
{
	switch (supervisor->state)
	{
		case READING_QUOTE:
			quote_char(supervisor, c);
			return _feed_char(supervisor, c, TRUE);
			break;
		
		default:
			supervisor->current->llsFirst = supervisor->next->head;
			supervisor->next->head = NULL;
			
			supervisor->thisChar = supervisor->next->thisChar;
			
			dispose_reader(supervisor->next);
			supervisor->next = NULL;
	
			_feed_char(supervisor, c, TRUE);
			break;
	}
	
	return supervisor->state;
}

static long quote_char(AtomReader *ar, char x)
{
	if (ar->next->state == READING_END)
	{
		ar->head = make_list(make_atom_symbol("QUOTE"),
								 ar->next->head,
								 NULL);
		if (ar->head == NULL)
		{
			dispose_reader(ar->next);
			ar->next = NULL;
			ar->state = READING_ERROR;
			return ar->state;
		}
		ar->next->head = NULL;
		ar->thisChar = ar->next->thisChar;
		dispose_reader(ar->next);
		ar->next = NULL;
		ar->state = READING_END;
	}
	else
	{
		close_reader(ar->next);			/* this closes our gopher and 
                                           calls us again. */
	}
	
	return ar->state;
}


long _feed_char(AtomReader *ar, char c, int recursive)
{
	AtomReader	*gopher;
	long state;
	
	if (ar == NULL)
		return READING_ERROR;
	
	gopher = ar;
	
	while (gopher->next)
	{
		gopher = gopher->next;
	}

	if (!recursive)
	{
		gopher->thisChar = c;
	}

	switch (gopher->state)
	{
		case READING_STRING:
			string_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_END:
			if (gopher->itsSupervisor)
			{
				return unwind(gopher->itsSupervisor, (char) gopher->thisChar);
			}
			else
				return READING_ERROR;
			break;
		
		case READING_WHITE:
			if (!iswhite(gopher->thisChar))
			{
				gopher->state = gopher->nextState;
				_feed_char(gopher, c, TRUE);
			}
			break;
		
		case READING_SYMBOL:
			state = symbol_char(gopher, (char) gopher->thisChar);
			if (gopher->state == READING_END)
			{
				if (gopher->itsSupervisor)
					return unwind(gopher->itsSupervisor, 
                                  (char) gopher->thisChar);
			}
			break;
			
		case READING_BEGIN:
			begin_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_INT:
		case READING_DBREF:
			state = number_char(gopher, (char) gopher->thisChar);
			if (gopher->state == READING_END)
			{
				if (gopher->itsSupervisor)
					return unwind(gopher->itsSupervisor, 
                                  (char) gopher->thisChar);
			}
			break;

		case READING_MINUS:
			minus_char(gopher, (char) gopher->thisChar);
			break;

		case READING_PLUS:
			plus_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_DBREF_TOKEN:
			dbref_token_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_PAIR:
			pair_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_BASE64:
			base64_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_HEX:
			hex_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_CAPSULE:
			capsule_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_CANONSTRING:
			canonical_string_char(gopher, (char) gopher->thisChar);
			break;
		
		case READING_QUOTE:
			quote_char(gopher, (char) gopher->thisChar);
			break;
		
		default:
			return READING_ERROR;
	}

	return gopher->state;
}

#if 0
long feed_char(AtomReader *ar, char c)
{
	return _feed_char(ar, c, FALSE);
}
#endif

static AtomWriter *make_writer(long lineLength, long howPretty)
{
	AtomWriter *writer;

	writer = ALLOCATE_CLEARED(1, AtomWriter);
	if (writer == NULL)
		return NULL;

	writer->bufferLength = lineLength;
	writer->howPretty = howPretty;
	writer->state = WRITING_BEGIN;

	return writer;
}

AtomWriter *create_writer(Atom *theAtom, long lineLength, long howPretty)
{
	AtomWriter *writer;
	
	if ((!IS_VALID_ATOM(theAtom)) || lineLength < MIN_LINE_LENGTH)
	{
		return NULL;
	}
	
	writer = make_writer(lineLength, howPretty);
		
	if (writer == NULL)
		return NULL;
	
	setf(&writer->head, copy_atom(theAtom));
	writer->current = writer->head;
	
	if (writer->head == NULL)
	{
		DEALLOCATE(writer);
		return NULL;
	}
	
	setf(&writer->buffer, create_string(lineLength));
	if (writer->buffer == NULL)
	{
		setf(&writer->head, NULL);
		DEALLOCATE(writer);
		return NULL;
	}
	
	return writer;
}

void dispose_writer(AtomWriter *aw)
{
	if (aw == NULL)
		return;
	
	if (aw->next)
		dispose_writer(aw->next);
	
	if (aw->itsSupervisor)
	{
		aw->itsSupervisor->next = NULL;		/* clear pointer to us. */
		aw->itsSupervisor = NULL;
	}

	if (aw->buffer)
		setf(&aw->buffer, NULL);
	
	if (aw->head)
		setf(&aw->head, NULL);
		
	DEALLOCATE (aw);
	return;
}

static void write_symbol(AtomWriter *aw)
{
#ifdef BREAK_SYMBOLS
	long leftToPrint = (aw->current->llsStringLen - aw->stringPos);
	long remainingInBuffer = aw->bufferLength - 
                            (aw->buffer->llsStringLen + 1);
	
	if (leftToPrint <= remainingInBuffer)
	{
		strcpy(aw->buffer->llsString + aw->buffer->llsStringLen, 
			   aw->current->llsString + aw->stringPos);
		aw->state = WRITING_END;
		aw->stringPos = 0;
	}
	else
	{
		memcpy(&aw->buffer->llsString[aw->buffer->llsStringLen], 
				aw->current->llsString + aw->stringPos, 
				remainingInBuffer);
		aw->buffer->llsStringLen += remainingInBuffer;
		aw->buffer->llsString[aw->buffer->llsStringLen] = '\0';
		aw->stringPos += remainingInBuffer;
		aw->state = WRITING_SYMBOL;
	}
#else

	print_into(aw->buffer, aw->current);
	aw->state = WRITING_END;
	aw->stringPos = 0;

#endif
}

static void write_base64(AtomWriter *aw)
{
	long leftToPrint = (aw->current->llsStringLen - aw->stringPos);
	long remainingInBuffer = aw->bufferLength - (aw->buffer->llsStringLen + 1);
	char base64[5];
	
	aw->state = WRITING_BASE64;
	aw->substate = SUBSTATE_NORMAL;

	if (aw->stringPos == 0)
	{
		if (remainingInBuffer > 8)		/* Don't start if there's too 
                                            little room. */
		{
			append_atom_char(aw->buffer, '|');
			remainingInBuffer--;
		}
		else
		{
			return;
		}
	}
	
	while (remainingInBuffer > 5 && 
	       aw->stringPos < aw->current->llsStringLen)
	{
		base64_chunk(&aw->current->llsString[aw->stringPos], base64, 3);
		append_atom_string(aw->buffer, base64);
		
		aw->stringPos += 3;
		remainingInBuffer -= 3;
	}

	if (aw->stringPos >= aw->current->llsStringLen)		/* Done? */
	{
		append_atom_char(aw->buffer, '|');
		aw->state = WRITING_END;
	}
}

static void write_string(AtomWriter *aw)
{
	long leftToPrint = (aw->current->llsStringLen - aw->stringPos);
	long remainingInBuffer = aw->bufferLength - 
                            (aw->buffer->llsStringLen + 1);
	unsigned long c, len;
	char	buf[16];

	aw->state = WRITING_STRING;
	aw->substate = SUBSTATE_NORMAL;

	if (aw->stringPos == 0)
	{
		if (remainingInBuffer > 8)		/* Don't start if there's little room. */
		{
			append_atom_char(aw->buffer, '\"');
			remainingInBuffer--;
		}
		else
		{
			return;
		}
	}
	
	while (remainingInBuffer > 2 && aw->stringPos < aw->current->llsStringLen)
	{
		c = aw->current->llsString[aw->stringPos];
		
		if (c == '\"' || c == '\\')
		{
			if (remainingInBuffer > 1)		/* look for padding */
			{
				append_atom_char(aw->buffer, '\\');
				append_atom_char(aw->buffer, (char) c);
				aw->stringPos++;
				remainingInBuffer -= 2;
			}
			else
				remainingInBuffer = 0;		/* just exit. */
			aw->substate = SUBSTATE_NORMAL;
		}
		else if (c == 0x7f || (c < 0x20 && c != '\t') ||	/* DEL, or C0 & not tab */
				 (aw->substate == SUBSTATE_JUST_QUOTED &&	/* or we just quoted a char */
				  c >= '0' && c <= '7'))					/* and this is an octal digit */
		{
			if (remainingInBuffer > 4)		/* Near margin? */
			{
				sprintf(buf, "\\%o", c & 0xff);		/* Another 1-octet assumption. */
				len = strlen(buf);
				remainingInBuffer -= len;
				append_atom_string(aw->buffer, buf);
				aw->stringPos++;

				aw->substate = SUBSTATE_JUST_QUOTED;
				/* This substate tells us that an octal digit following should */
				/* also be quoted. */
			}
		}
		else
		{
			append_atom_char(aw->buffer, (char) c);
			aw->stringPos++;
			remainingInBuffer--;
			aw->substate = SUBSTATE_NORMAL;
		}
	}
	
	if (aw->stringPos >= aw->current->llsStringLen)		/* Done? */
	{
		append_atom_char(aw->buffer, '\"');
		aw->state = WRITING_END;
	}
}

static int can_fit(AtomWriter *aw, Atom *a)
{
	long remainingInBuffer = aw->bufferLength - (aw->buffer->llsStringLen + 1);

	if (NUMBER_P(a) || SYMBOL_P(a))
		return 1;
	else if (TEXT_P(a) && a->llsStringLen < remainingInBuffer)
		return 1;
	else if (PAIR_P(a) && remainingInBuffer >= 10)
		return 1;
	else if (remainingInBuffer >= 10)
		return 1;
	else
		return 0;
}

static void begin_writer(AtomWriter *aw)
{
	aw->stringPos = 0;

	switch (aw->current->tag)
	{
		case INT_ATOM:				/* We're at the beginning, just print these. */
		case DBREF_ATOM:
			print_into(aw->buffer, aw->current);
			aw->state = WRITING_END;
			break;
		
		case SYMBOL_ATOM:			/* Print if we can. */
			write_symbol(aw);
			break;
		
		case STRING_ATOM:
			write_string(aw);
			break;
		
		case PAIR_ATOM:
			write_pair(aw);
			break;

		case WRITING_BASE64:
			write_base64(aw);
			break;
	}
}

static void select_writer_action(AtomWriter *aw)
{
	if (aw->next)
		select_writer_action(aw->next);

	switch (aw->state)
	{
		case WRITING_BEGIN:
			begin_writer(aw);
			break;
		
		case WRITING_END:
			if (aw->itsSupervisor == NULL)
			{
				aw->buffer->llsString[0] = '\0';
				break;
			}
			else
			{
				aw = aw->itsSupervisor;
				dispose_writer(aw->next);
				aw->next = NULL;
				if (PAIR_P(aw->current))
					aw->current = aw->current->llsRest;
				select_writer_action(aw);
				return;
			}
		
		case WRITING_STRING:
			write_string(aw);
			break;
		
		case WRITING_SYMBOL:
			write_symbol(aw);
			break;
		
		case WRITING_PAIR:
			write_pair(aw);
			break;
		
		case WRITING_BASE64:
			write_base64(aw);
			break;
	}
#if 0
	if (aw->state == WRITING_END && 
		aw->itsSupervisor != NULL &&
		(aw->bufferLength - (aw->buffer->llsStringLen + 1) > 3))
	{
		aw = aw->itsSupervisor;
		dispose_writer(aw->next);
		if (PAIR_P(aw->current))
			aw->current = aw->current->llsRest;
		select_writer_action(aw);
	}
#endif
}

static void handle_writing_end(AtomWriter *aw)
{
	dispose_writer(aw->next);
	aw->next = NULL;
	aw->current = aw->current->llsRest;

	if (aw->current == NULL)
	{
		append_atom_char(aw->buffer, ')');
		aw->state = WRITING_END;
	}
}

static void write_pair(AtomWriter *aw)
{
	long remainingInBuffer = aw->bufferLength - (aw->buffer->llsStringLen + 1);

	aw->state = WRITING_PAIR;

	if (aw->next)
	{
		if (aw->next->state == WRITING_END)
			handle_writing_end(aw);
		if (aw->state == WRITING_END)
			return;
	}

	if (aw->current == NULL)				/* At end of list? */
	{
		if (remainingInBuffer > 0)
		{
			append_atom_char(aw->buffer, ')');
			aw->state = WRITING_END;
		}
		return;
	}

	if (aw->current->llsFirst == NULL && aw->current->llsRest == NULL)
	{
		append_atom_string(aw->buffer, "()");
		aw->state = WRITING_END;
		return;
	}

	if (aw->head == aw->current)			/* At beginning of list? */
	{
		if (can_fit(aw, aw->current))
			append_atom_char(aw->buffer, '(');
		else
			return;
	}

	while (aw->current && (aw->head == aw->current || can_fit(aw, aw->current)))
	{
		if (aw->head != aw->current)
			append_atom_char(aw->buffer, ' ');
		
		aw->next = make_writer(aw->bufferLength, aw->howPretty);
		if (aw->next == NULL)
		{
			aw->state = WRITING_ERROR;
			return;
		}
		
		aw->next->itsSupervisor = aw;
		setf(&aw->next->buffer, aw->buffer);
		setf(&aw->next->head, aw->current->llsFirst);
		aw->next->current = aw->next->head;
		begin_writer(aw->next);
		
		if (aw->next->state == WRITING_END)
		{
			handle_writing_end(aw);
			if (aw->state == WRITING_END)
				break;	
		}
		else
			break;
		
	remainingInBuffer = aw->bufferLength - (aw->buffer->llsStringLen + 1);
	}
}

static long bottom_writer_state(AtomWriter *aw)
{
	while (aw->next)
		aw = aw->next;
	
	return aw->state;
}

char *next_writer_line(AtomWriter *aw)
{
	long remainingInBuffer;
	
	if (aw == NULL)
		return NULL;
	
	aw->buffer->llsStringLen = 0;
	
	remainingInBuffer = aw->bufferLength - (aw->buffer->llsStringLen + 1);
	while (remainingInBuffer > 10)
	{
		select_writer_action(aw);
		remainingInBuffer = aw->bufferLength - (aw->buffer->llsStringLen + 1);
		if (aw->state == WRITING_END)
			break;
	}
	
	return aw->buffer->llsString;
}

