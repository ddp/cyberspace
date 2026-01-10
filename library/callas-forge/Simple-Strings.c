/*
// Mindless String Routines.
//
// Copyright 1993, 2004, Jonathan D. Callas. All Rights Reserved.
//
*/

#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#include "Simple-Strings.h"

char THE_NULL_STRING[] = "";

static char _lowercase[] = {      
	'Š', 'Œ', '', '', '–', 'š', 'Ÿ', '‡', 'ˆ', '‰', 'Š', '‹', 'Œ', '', '', '',
	'', '‘', '’', '“', '”', '•', '–', '—', '˜', '™', 'š', '›', 'œ', '', '', 'Ÿ',
	' ', '¡', '¢', '£', '¤', '¥', '¦', '§', '¨', '©', 'ª', '«', '¬', '­', '¾', '¿',
	'°', '±', '²', '³', '´', 'µ', '¶', '·', '¹', '¹', 'º', '»', '¼', '½', '¾', '¿',
	'À', 'Á', 'Â', 'Ã', 'Ä', 'Å', 'Æ', 'Ç', 'È', 'É', 'Ê', 'ˆ', '‹', '›', 'Ï', 'Ï',
	' ', ' ', 'Ò', 'Ó', 'Ô', 'Õ', 'Ö', '×', 'Ø', 'Ø', 'Ú', 'Û', 'Ü', 'İ', 'Ş', 'ß',
	'à', 'á', 'â', 'ã', 'ä', '‰', '', '‡', '‘', '', '’', '”', '•', '“', '—', '™',
	'ğ', '˜', 'œ', '', 'œ', 'õ', 'ö', '÷', 'ø', 'ù', 'ú', 'û', 'ü', 'ı', 'ş', 'ÿ',
	  0,   1,   2,   3,   4,   5,   6,   7,   8,   9,  10,  11,  12,  13,  14,  15,
	 16,  17,  18,  19,  20,  21,  22,  23,  24,  25,  26,  27,  28,  29,  30,  31,
	' ', '!', '"', '#', '$', '%', '&', '\'','(', ')', '*', '+', ',', ' ', '.', '/',
	'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', ':', ';', '<', '=', '>', '?',
	'@', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o',
	'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '[', '\\',']', '^', ' ',
	'`', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o',
	'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '{', '|', '}', '~', 127,
	'Š', 'Œ', '', '', '–', 'š', 'Ÿ', '‡', 'ˆ', '‰', 'Š', '‹', 'Œ', '', '', '',
	'', '‘', '’', '“', '”', '•', '–', '—', '˜', '™', 'š', '›', 'œ', '', '', 'Ÿ',
	' ', '¡', '¢', '£', '¤', '¥', '¦', '§', '¨', '©', 'ª', '«', '¬', '­', '¾', '¿',
	'°', '±', '²', '³', '´', 'µ', '¶', '·', '¹', '¹', 'º', '»', '¼', '½', '¾', '¿',
	'À', 'Á', 'Â', 'Ã', 'Ä', 'Å', 'Æ', 'Ç', 'È', 'É', 'Ê', 'ˆ', '‹', '›', 'Ï', 'Ï',
	' ', ' ', 'Ò', 'Ó', 'Ô', 'Õ', 'Ö', '×', 'Ø', 'Ø', 'Ú', 'Û', 'Ü', 'İ', 'Ş', 'ß',
	'à', 'á', 'â', 'ã', 'ä', '‰', '', '‡', '‘', '', '’', '”', '•', '“', '—', '™',
	'ğ', '˜', 'œ', '', 'œ', 'õ', 'ö', '÷', 'ø', 'ù', 'ú', 'û', 'ü', 'ı', 'ş', 'ÿ'
};

static char _uppercase[] = {
	'€', '', '‚', 'ƒ', '„', '…', '†', 'ç', 'Ë', 'å', '€', 'Ì', '', '‚', 'ƒ', 'é',
	'æ', 'è', 'ê', 'í', 'ë', 'ì', '„', 'î', 'ñ', 'ï', '…', 'Í', 'ò', 'ô', 'ó', '†',
	' ', '¡', '¢', '£', '¤', '¥', '¦', '§', '¨', '©', 'ª', '«', '¬', '­', '®', '¯',
	'°', '±', '²', '³', '´', 'µ', '¶', '·', '¸', '¸', 'º', '»', '¼', '½', '®', '¯',
	'À', 'Á', 'Â', 'Ã', 'Ä', 'Å', 'Æ', 'Ç', 'È', 'É', 'Ê', 'Ë', 'Ì', 'Í', 'Î', 'Î',
	'Ğ', 'Ñ', 'Ò', 'Ó', 'Ô', 'Õ', 'Ö', '×', 'Ù', 'Ù', 'Ú', 'Û', 'Ü', 'İ', 'Ş', 'ß',
	'à', 'á', 'â', 'ã', 'ä', 'å', 'æ', 'ç', 'è', 'é', 'ê', 'ë', 'ì', 'í', 'î', 'ï',
	'ğ', 'ñ', 'ò', 'ó', 'ô', 'I', 'ö', '÷', 'ø', 'ù', 'ú', 'û', 'ü', 'ı', 'ş', 'ÿ',
	  0,   1,   2,   3,   4,   5,   6,   7,   8,   9,  10,  11,  12,  13,  14,  15,
	 16,  17,  18,  19,  20,  21,  22,  23,  24,  25,  26,  27,  28,  29,  30,  31,
	'-', '!', '"', '#', '$', '%', '&', '\'','(', ')', '*', '+', ',', '-', '.', '/',
	'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', ':', ';', '<', '=', '>', '?',
	'@', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O',
	'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', '[', '\\',']', '^', '_',
	'`', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O',
	'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', '{', '|', '}', '~', 127,
	'€', '', '‚', 'ƒ', '„', '…', '†', 'ç', 'Ë', 'å', '€', 'Ì', '', '‚', 'ƒ', 'é',
	'æ', 'è', 'ê', 'í', 'ë', 'ì', '„', 'î', 'ñ', 'ï', '…', 'Í', 'ò', 'ô', 'ó', '†',
	' ', '¡', '¢', '£', '¤', '¥', '¦', '§', '¨', '©', 'ª', '«', '¬', '­', '®', '¯',
	'°', '±', '²', '³', '´', 'µ', '¶', '·', '¸', '¸', 'º', '»', '¼', '½', '®', '¯',
	'À', 'Á', 'Â', 'Ã', 'Ä', 'Å', 'Æ', 'Ç', 'È', 'É', 'Ê', 'Ë', 'Ì', 'Í', 'Î', 'Î',
	'Ğ', 'Ñ', 'Ò', 'Ó', 'Ô', 'Õ', 'Ö', '×', 'Ù', 'Ù', 'Ú', 'Û', 'Ü', 'İ', 'Ş', 'ß',
	'à', 'á', 'â', 'ã', 'ä', 'å', 'æ', 'ç', 'è', 'é', 'ê', 'ë', 'ì', 'í', 'î', 'ï',
	'ğ', 'ñ', 'ò', 'ó', 'ô', 'I', 'ö', '÷', 'ø', 'ù', 'ú', 'û', 'ü', 'ı', 'ş', 'ÿ'
};

char *lowercase = (char *) &(_lowercase[128]);
char *uppercase = (char *) &(_uppercase[128]);

int string_compare(char *s, char *t)
{
	if (!s)
		s = THE_NULL_STRING;
	if (!t)
		t = THE_NULL_STRING;
	while (*s && *t && lowercase[*s] == lowercase[*t])
	{
  		s++; t++;
  	}
  
	return lowercase[*s] - lowercase[*t];
}

int stringn_compare(char *s, char *t, int n)
{
	if (0 == n) 
		return 0;
	if (NULL == s)
		s = THE_NULL_STRING;
	if (NULL == t)
		t = THE_NULL_STRING;
	
	while (--n && *s && *t && lowercase[*s] == lowercase[*t])
	{
		s++;
		t++;
	}
  
	return lowercase[*s] - lowercase[*t];
}

int string_prefix(char *string, char *prefix)
{
	while (*string && *prefix && lowercase[*string] == lowercase[*prefix])
	{
		string++;
		prefix++;
	}
  return *prefix == '\0';
}

/* True for nonempty matches starting at the beginning of a word */

char *string_match(char *string, char *substring)
{
	if (substring && *substring)
	{
		while (*string)
		{
			if (string_prefix(string, substring))	/* A hit? */
				return string;
				
			/* Find next word */
			while (*string && isalnum(*string))		/* to end */
				string++;
			while (*string && !isalnum(*string))	/* to beginning */
				string++;
		}
	}
	return 0;
}

#if !MEMORY_CHECK
char *dup_string(char *string)
{
	char *s;

	/* Return NULL as a shorthand for a "" string. */

	if (string == NULL || *string == '\0')
		return NULL;							/*/// Turn this around someday */

	if ((s = (char *) calloc (strlen(string)+1, sizeof (char))) == NULL)
		abort();

	strcpy(s, string);
	return s;
}
#endif

void lowerstring(char *string)
{
	if (!string)
		return;

	while (*string)
	{
		*string = lowercase[*string];
		string++;
	}
}

void uppercase_string(char *string)
{
	if (!string)
		return;

	while (*string)
	{
		*string = uppercase[*string];
		string++;
	}
}

long capitalize(char *string)
{
	char *s = string;
	
	char lowerspace = lowercase[' '];
	
	if (!string)
		return 0;

	if (*string)
		*string++ = uppercase[*string];

	while (*string && lowercase[*string] != lowerspace)
	{
		*string = lowercase[*string];
		string++;
	}
	
	return string - s;
}

void capitalize_string(char *string)
{
	char lowerspace = lowercase[' '];

	if (!string)
		return;
	
	while (*string)
	{
		string += capitalize(string);
		while (*string && *string == lowerspace)
			string++;
	}
}

