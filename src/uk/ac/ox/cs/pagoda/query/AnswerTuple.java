package uk.ac.ox.cs.pagoda.query;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.semanticweb.HermiT.model.Constant;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.model.Term;
import org.semanticweb.HermiT.model.Variable;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.util.Namespace;

public class AnswerTuple {
	
	public static final String SEPARATOR = "\t";
	
	String m_str = null; 
	String[] m_tuple; 

	public AnswerTuple(String string) {
		m_str = string; 
		m_tuple = string.split(SEPARATOR); 
	}
	
	public AnswerTuple(TupleIterator iter) {
		int arity = 0;
		try {
			arity = iter.getArity();
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} 
		m_tuple = new String[arity];
		try {
			for (int i = 0; i < arity; ++i)
				m_tuple[i] = RDFoxTripleManager.getRawTerm(iter.getResource(i));
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} 
	}
	
	public AnswerTuple(String[] strs) {
		m_tuple = strs; 
	}
	
	public AnswerTuple(Collection<String> list) {
		m_tuple = new String [list.size()]; 
		list.toArray(m_tuple); 
	}
	
	public int getArity() {
		return m_tuple.length; 
	}

	public String getRawTerm(int index) {
		if (m_tuple[index].startsWith("<"))
			return m_tuple[index]; 
		return MyPrefixes.PAGOdAPrefixes.getQuotedIRI(m_tuple[index]); 
		 
	}
	
	public int hashCode() {
		return toString().hashCode(); 
	}
	
	public boolean equals(Object obj) {
		return toString().equals(obj.toString()); 
	}
	
	public String toString() {
		if (m_str != null) return m_str; 
		StringBuilder sb = new StringBuilder();  
		for (int i = 0; i < m_tuple.length; ++i) {
			if (sb.length() != 0) sb.append(SEPARATOR);
			sb.append(m_tuple[i]); 
		}
		return m_str = sb.toString();  
	}

	public String getValue(String var, String[] vars) {
		for (int i = 0; i < vars.length; ++i)
			if (vars[i].equals(var))
				return m_tuple[i]; 
		return null;
	}

	public Map<Variable, Term> getAssignment(String[] vars) {
		Map<Variable, Term> map = new HashMap<Variable, Term>(); 
		int index = 0; 
		for (String var: vars) {
			map.put(Variable.create(var), m_tuple[index].startsWith("\"") ? Constant.create(m_tuple[index], Namespace.XSD_STRING) : Individual.create(m_tuple[index++])); 
		}
		return map; 
	}
	
}
