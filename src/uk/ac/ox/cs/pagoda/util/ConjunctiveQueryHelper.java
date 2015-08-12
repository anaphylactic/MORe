package uk.ac.ox.cs.pagoda.util;

import java.util.Collection;
import java.util.LinkedList;

public class ConjunctiveQueryHelper {
	
	public static String[] getAnswerVariables(String queryText) {
		String[] answerVariables = null; 
		for (String line: queryText.split("\n")) 
			if (line.length() > 6 && line.substring(0, 6).equalsIgnoreCase("SELECT")) {
				if (line.contains("*")) 
					return getAllVariables(queryText).toArray(new String[0]); 
				int index = line.indexOf("{"); 
				if (index != -1) line = line.substring(0, index - 1); 
				
				String[] terms = line.split(" ");
				int num = 0; 
				for (int i = 0; i < terms.length; ++i)
					if (terms[i].startsWith("?")) ++num;
				answerVariables = new String[num]; 
				for (int i = 0, j = 0; i < terms.length; ++i)
					if (terms[i].startsWith("?"))
						answerVariables[j++] = terms[i].substring(1);
				break; 
			}
		return answerVariables;
	}

	private static Collection<String> getAllVariables(String queryText) {
		Collection<String> vars = new LinkedList<String>(); 
		int start, end = 0; 
		while ((start = queryText.indexOf("?", end)) != -1) {
			end = start + 1; 
			while (end + 1 < queryText.length() && !Character.isSpaceChar(queryText.charAt(end + 1))) ++end;
			vars.add(queryText.substring(start + 1, end + 1)); 
		}
		return vars; 
	}

}
