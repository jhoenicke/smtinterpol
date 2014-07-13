package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.Reader;

public class Main {
	public static void main(String[] param) throws Exception {
		Reader reader = new InputStreamReader(System.in);
		String filename = "<stdin>";
		if (param.length > 0) {
			filename = param[0];
			reader = new FileReader(filename);
		}
		MySymbolFactory symfactory = new MySymbolFactory();
		Lexer lexer = new Lexer(reader);
		lexer.setSymbolFactory(symfactory);
		Parser parser = new Parser(lexer, symfactory);
		parser.setFileName(filename);
		parser.parse();
	}
}
