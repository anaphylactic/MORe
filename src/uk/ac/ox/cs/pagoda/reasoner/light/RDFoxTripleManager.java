package uk.ac.ox.cs.pagoda.reasoner.light;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import org.semanticweb.HermiT.model.AnnotatedEquality;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.Constant;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.Equality;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.model.Inequality;
import org.semanticweb.HermiT.model.Term;
import org.semanticweb.HermiT.model.Variable;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.model.Datatype;
import uk.ac.ox.cs.JRDFox.model.GroundTerm;
import uk.ac.ox.cs.JRDFox.store.DataStore;
import uk.ac.ox.cs.JRDFox.store.DataStore.UpdateType;
import uk.ac.ox.cs.JRDFox.store.Dictionary;
import uk.ac.ox.cs.JRDFox.store.Resource;
import uk.ac.ox.cs.pagoda.owl.OWLHelper;
import uk.ac.ox.cs.pagoda.util.Namespace;

public class RDFoxTripleManager {
	
	UpdateType m_incrementally; 
//	boolean m_incrementally; 

	DataStore m_store;
	Dictionary m_dict; 
	Set<Atom> triplesByTerm = new HashSet<Atom>();
	
	public RDFoxTripleManager(DataStore store, boolean incrementally) {
		m_store = store;
//		m_incrementally = incrementally; 
		if (incrementally)
			m_incrementally = UpdateType.ScheduleForAddition;
		else 
			m_incrementally = UpdateType.Add; 
		
		try {
			m_dict = store.getDictionary();
			resourceID = m_dict.resolveResources(
					new String[] {Namespace.RDF_TYPE,  Namespace.EQUALITY, Namespace.INEQUALITY},
					new Datatype[] {Datatype.IRI_REFERENCE, Datatype.IRI_REFERENCE, Datatype.IRI_REFERENCE} 
					); 
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}
	}
	
	public boolean isRdfTypeID(long id) {
		return id == resourceID[0]; 
	}
	
	public void addTripleByID(long[] tuple) {
		try {
			m_store.addTriplesByResourceIDs(tuple, m_incrementally);
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}
	}
	
	public void addTripleByTerm(Atom atom) {
		try {
			m_store.addTriples(getRDFoxTriple(atom), m_incrementally);
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} 
	}
	
	public static GroundTerm[] getRDFoxTriple(Atom instance) {
		if (instance.getArity() == 1) 
			return new GroundTerm[] {
					uk.ac.ox.cs.JRDFox.model.Individual.create(((Individual) instance.getArgument(0)).getIRI()), 
					uk.ac.ox.cs.JRDFox.model.Individual.RDF_TYPE, 
					uk.ac.ox.cs.JRDFox.model.Individual.create(((AtomicConcept) instance.getDLPredicate()).getIRI()) };
		else if (instance.getDLPredicate() instanceof Equality || instance.getDLPredicate() instanceof AnnotatedEquality) 
			return new GroundTerm[] {
					uk.ac.ox.cs.JRDFox.model.Individual.create(((Individual) instance.getArgument(0)).getIRI()), 
					uk.ac.ox.cs.JRDFox.model.Individual.SAME_AS, 
					uk.ac.ox.cs.JRDFox.model.Individual.create(((Individual) instance.getArgument(1)).getIRI()) };
		else if (instance.getDLPredicate() instanceof Inequality) 
			return new GroundTerm[] {
					uk.ac.ox.cs.JRDFox.model.Individual.create(((Individual) instance.getArgument(0)).getIRI()), 
					uk.ac.ox.cs.JRDFox.model.Individual.DIFFERENT_FROM, 
					uk.ac.ox.cs.JRDFox.model.Individual.create(((Individual) instance.getArgument(1)).getIRI()) }; 
		else 
			return new GroundTerm[] {
					uk.ac.ox.cs.JRDFox.model.Individual.create(((Individual) instance.getArgument(0)).getIRI()), 
					uk.ac.ox.cs.JRDFox.model.Individual.create(((AtomicRole) instance.getDLPredicate()).getIRI()), 
					uk.ac.ox.cs.JRDFox.model.Individual.create(((Individual) instance.getArgument(1)).getIRI()) };
	}
	
	long[] resourceID; // rdf:type, owl:sameAs, owl:differentFrom 

	public long[] getInstance(Atom atom, Map<Variable, Integer> assignment) {
		DLPredicate p = atom.getDLPredicate(); 
		if (p instanceof Equality || p instanceof AnnotatedEquality) 
			return new long[] {
					getResourceID(atom.getArgument(0), assignment),
					resourceID[1],
					getResourceID(atom.getArgument(1), assignment)
			}; 
		else if (p instanceof Inequality) 
			return new long[] {
					getResourceID(atom.getArgument(0), assignment), 
					resourceID[2], 
					getResourceID(atom.getArgument(1), assignment)
			}; 
		else if (atom.getArity() == 1) 
			return new long[] {
					getResourceID(atom.getArgument(0), assignment), 
					resourceID[0], 
					getResourceID(p)
			}; 
		else 
			return new long[] {
					getResourceID(atom.getArgument(0), assignment), 
					getResourceID(p), 
					getResourceID(atom.getArgument(1), assignment)
			}; 
	}
	
	public String getRawTerm(long id) {
		Resource[] res = new Resource[1]; 
		try {
			m_dict.getResources(new long[] {id}, 0, 1, res);
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}
		return getRawTerm(res[0]); 
	}

	Map<String, Long> predicateCache = new HashMap<String, Long>(); 
	
	public long getResourceID(DLPredicate p) {
		Long id; 
		String name = p instanceof AtomicConcept ? ((AtomicConcept) p).getIRI() : ((AtomicRole) p).getIRI();
		if ((id = predicateCache.get(name)) != null) return id;
		try {
			predicateCache.put(name, id = resolveResource(name, Datatype.IRI_REFERENCE));
			
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		} 
		return id;
	}
	
	public long getResourceID(String name) {
		Long id = null; 
		try {
			id =  resolveResource(name, Datatype.IRI_REFERENCE); 
		} catch (JRDFStoreException e) {
			e.printStackTrace();
		}
		return id; 
	}
	
	private long resolveResource(String name, Datatype type) throws JRDFStoreException {
		String[] lexicalForms = new String[] {name}; 
		Datatype[] types = new Datatype[] {type};
		return m_dict.resolveResources(lexicalForms, types)[0]; 
	}
	
	Map<Term, Long> termCache = new HashMap<Term, Long>(); 
	Queue<Term> termList = new LinkedList<Term>();
	int sizeLimit = 10000; 

	private long getResourceID(Term arg, Map<Variable, Integer> assignment) {
		while (termCache.size() > sizeLimit) 
			termCache.remove(termList.poll()); 
		
		if (arg instanceof Variable) return assignment.get((Variable) arg); 
		Long id = null; 
		if ((id = termCache.get(arg)) != null)
			return id; 
		
//		if (arg instanceof Individual) {
			try {
				if (arg instanceof Individual)
					termCache.put(arg, id = resolveResource(((Individual) arg).getIRI(), Datatype.IRI_REFERENCE)); 
				else if (arg instanceof Constant)
					termCache.put(arg, id = resolveResource(((Constant) arg).getLexicalForm(), getDatatype(((Constant) arg).getDatatypeURI()))); 
				
			} catch (JRDFStoreException e) {
				e.printStackTrace();
			} 
//		}
			
		return id;
	}
	
	private static int getDatatypeID(String uri) {
		if (uri.equals("http://www.w3.org/2001/XMLSchema#string")) return Datatype.XSD_STRING.value(); 
		if (uri.equals("http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")) return Datatype.RDF_PLAIN_LITERAL.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#integer")) return Datatype.XSD_INTEGER.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#float")) return Datatype.XSD_FLOAT.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#double")) return Datatype.XSD_DOUBLE.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#boolean")) return Datatype.XSD_BOOLEAN.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#dateTime")) return Datatype.XSD_DATE_TIME.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#time")) return Datatype.XSD_TIME.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#date")) return Datatype.XSD_DATE.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gYearMonth")) return Datatype.XSD_G_YEAR_MONTH.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gYear")) return Datatype.XSD_G_YEAR.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gMonthDay")) return Datatype.XSD_G_MONTH_DAY.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gDay")) return Datatype.XSD_G_DAY.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gMonth")) return Datatype.XSD_G_MONTH.value(); 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#duration")) return Datatype.XSD_DURATION.value(); 
		
		return -1;
	}
	
	private static Datatype getDatatype(String uri) {
		if (uri.equals("http://www.w3.org/2001/XMLSchema#string")) return Datatype.XSD_STRING; 
		if (uri.equals("http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")) return Datatype.RDF_PLAIN_LITERAL; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#integer")) return Datatype.XSD_INTEGER; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#float")) return Datatype.XSD_FLOAT; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#double")) return Datatype.XSD_DOUBLE; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#boolean")) return Datatype.XSD_BOOLEAN; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#dateTime")) return Datatype.XSD_DATE_TIME; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#time")) return Datatype.XSD_TIME; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#date")) return Datatype.XSD_DATE; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gYearMonth")) return Datatype.XSD_G_YEAR_MONTH; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gYear")) return Datatype.XSD_G_YEAR; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gMonthDay")) return Datatype.XSD_G_MONTH_DAY; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gDay")) return Datatype.XSD_G_DAY; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#gMonth")) return Datatype.XSD_G_MONTH; 
		if (uri.equals("http://www.w3.org/2001/XMLSchema#duration")) return Datatype.XSD_DURATION; 
		
		return null;
	}

	public long[] getResourceIDs(Collection<uk.ac.ox.cs.JRDFox.model.Individual> individuals) {
		String[] str = new String[individuals.size()]; 
		Datatype[] types = new Datatype[individuals.size()]; 
		int index = 0; 
		for (uk.ac.ox.cs.JRDFox.model.Individual individual : individuals) {
			types[index] = Datatype.IRI_REFERENCE; 
			str[index++] = individual.getIRI(); 
		}
			
		try {
			return m_dict.resolveResources(str, types);
		} catch (JRDFStoreException e) {
			e.printStackTrace();
			return null; 
		} 
	}
	
	public static String getRawTerm(Resource r) {
		if (r.m_datatype.equals(Datatype.IRI_REFERENCE))
			return OWLHelper.addAngles(r.m_lexicalForm); 
		if (r.m_datatype.equals(Datatype.RDF_PLAIN_LITERAL))
			return r.m_lexicalForm;
		else 
			return r.m_lexicalForm + "^^" + r.m_datatype.getIRI(); 
	}
	
}
