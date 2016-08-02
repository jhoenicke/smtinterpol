package de.uni_freiburg.informatik.ultimate.smtinterpol.itt;

import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.Reader;

import java.util.HashMap;
import java.util.HashSet;

public class Main {
	MySymbolFactory symfactory = new MySymbolFactory();

	HashMap<String, Term> globals;
	{
		globals = new HashMap<String,Term>();
		globals.put("Prop", Term.PROP);
		globals.put("U", Term.universe(0));
	}
	HashSet<String> parsedFiles = new HashSet<String>();

	public Term lookupGlobal(String id) {
		if (globals.containsKey(id)) {
			return globals.get(id);
		}
		if (id.startsWith("U")) {
			try {
				int num = Integer.parseInt(id.substring(1));
				return Term.universe(num);
			} catch (NumberFormatException ex) {
				/* ignore */
			}
		}
		return null;
	}

	public void addDefinition(String name, Term expr) {
		globals.put(name, expr);
	}

	public void registerType(InductiveType type) {
		for (int i = 0; i < type.mConstrs.length; i++) {
			addDefinition(type.mConstrs[i].toString(), type.mConstrs[i]);
		}
		addDefinition(type.mRecOperator.toString(), type.mRecOperator);
	}

	public void parseFile(String filename) throws Exception {
		if (parsedFiles.contains(filename))
			return;
		Reader reader = filename.equals("<stdin>")
			? new InputStreamReader(System.in)
			: new FileReader(filename);
		Lexer lexer = new Lexer(reader);
		lexer.setSymbolFactory(symfactory);
		Parser parser = new Parser(lexer, symfactory);
		parser.setContext(this);
		parser.setFileName(filename);
		parser.parse();
		parsedFiles.add(filename);
	}

	public static void main(String[] param) throws Exception {
		String filename = "<stdin>";
		if (param.length > 0) {
			filename = param[0];
		}
		new Main().parseFile(filename);
	}
}
