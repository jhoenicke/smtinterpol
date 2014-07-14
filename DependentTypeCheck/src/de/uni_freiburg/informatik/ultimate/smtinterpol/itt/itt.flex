/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
/* ITT lexer */
package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java_cup.runtime.Symbol;

/**
 * This is a autogenerated lexer for the smtlib 2 script files.
 * It is generated from smtlib.flex by JFlex.
 */
%%

%class Lexer
%public
%unicode
%cup
%line
%column

%{
	private MySymbolFactory symFactory;

	public void setSymbolFactory(MySymbolFactory factory) {
		symFactory = factory;
	}

	private Symbol symbol(int type) {
		return symFactory.newSymbol(yytext(), type, yyline+1, yycolumn, yyline+1, yycolumn+yylength());
	}

	private Symbol symbol(int type, Object value) {
		return symFactory.newSymbol(yytext(), type, yyline+1, yycolumn, yyline+1, yycolumn+yylength(), value);
	}
%}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
WhiteSpace     = {LineTerminator} | [ \t\f]

/* comments */
Comment = {EndOfLineComment}

EndOfLineComment     = ";" {InputCharacter}* {LineTerminator}?
SMTLetter = [:letter:] | [~!@$%\^&*_+\-=<>.?/] 
SMTLetterDigit = {SMTLetter} | [:digit:]

Numeral = 0 | [1-9][0-9]*
Decimal = {Numeral} "."  0* {Numeral}
HexaDecimal = "#x" [0-9a-fA-F]+
QuotedSymbol = "|" [^|]* "|"
Symbol = {SMTLetter} {SMTLetterDigit}* 
Binary = "#b" [01]+

%state STRING

%%

<YYINITIAL>  {
  "("                    { return symbol(LexerSymbols.LPAR); }
  ")"                    { return symbol(LexerSymbols.RPAR); }
  "="                    { return symbol(LexerSymbols.EQUALS); }
  ":"                    { return symbol(LexerSymbols.COLON); }
  ","                    { return symbol(LexerSymbols.COMMA); }
  "->"                   { return symbol(LexerSymbols.ARROW); }
  "\\"                    { return symbol(LexerSymbols.LAMBDA); }

  /* Predefined Symbols */
  "Inductive"            { return symbol(LexerSymbols.INDUCTIVE, yytext()); }
  "Definition"           { return symbol(LexerSymbols.DEFINITION, yytext()); }
  "Check"                { return symbol(LexerSymbols.CHECK, yytext()); }
  "Eval"                 { return symbol(LexerSymbols.EVAL, yytext()); }

  /* Other Symbols and Keywords */
  {QuotedSymbol}         { return symbol(LexerSymbols.ID, yytext().substring(1, yylength()-1)); }
  {Symbol}               { return symbol(LexerSymbols.ID, yytext()); }
  
  /* Numbers and Strings */
  {Numeral}              { return symbol(LexerSymbols.ID, yytext()); }
  {Decimal}              { return symbol(LexerSymbols.ID, yytext()); }
  {HexaDecimal}          { return symbol(LexerSymbols.ID, yytext()); }
  {Binary}               { return symbol(LexerSymbols.ID, yytext()); }

 
  /* comments */
  {Comment}              { /* ignore */ }
 
  /* whitespace */
  {WhiteSpace}           { /* ignore */ }
}

/* error fallback */
.|\n                             { return symbol(LexerSymbols.error, yytext()); }

<<EOF>>                          { return symbol(LexerSymbols.EOF); }