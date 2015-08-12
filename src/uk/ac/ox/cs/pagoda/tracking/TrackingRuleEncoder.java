package uk.ac.ox.cs.pagoda.tracking;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.semanticweb.HermiT.model.AnnotatedEquality;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.Constant;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.DatatypeRestriction;
import org.semanticweb.HermiT.model.Equality;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.model.Inequality;
import org.semanticweb.HermiT.model.Variable;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.OWLOntology;

import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.query.AnswerTuple;
import uk.ac.ox.cs.pagoda.query.AnswerTuples;
import uk.ac.ox.cs.pagoda.query.GapTupleIterator;
import uk.ac.ox.cs.pagoda.query.QueryRecord;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.rules.UpperDatalogProgram;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Namespace;

public abstract class TrackingRuleEncoder {
	protected UpperDatalogProgram program;
	protected Collection<DLClause> trackingClauses = new HashSet<DLClause>();
	public Collection<DLClause> queryClauses = new LinkedList<DLClause>();
	
	Map<Integer, DLClause> index2clause = new HashMap<Integer, DLClause>();
	Map<DLClause, Integer> clause2index = new HashMap<DLClause, Integer>();
	
	String equalityRelatedRuleText = null; 
	protected BasicQueryEngine store;  
	
	public TrackingRuleEncoder(UpperDatalogProgram program, BasicQueryEngine store) {
		this.program = program;
		this.store = store; 
	}
	
	protected abstract String getEqualityRelatedRuleText();

	boolean ruleEncoded = false; 
	
	public boolean encodingRules() {
		if (ruleEncoded) return false;
		ruleEncoded = true; 
		
//		for (DLClause clause: program.getClauses(currentQuery.getClause())) {
		for (DLClause clause: program.getClauses()) {
			encodingRule(clause);
		}
		return true; 
	}
	
	protected String getIRI(String name) {
		return program.getOntology().getOntologyID().getOntologyIRI().toString() + "#" + name;
	}

	protected abstract void encodingRule(DLClause clause);
	
	protected Individual getIndividual4GeneralRule(DLClause clause) {
		clause = program.getCorrespondingClause(clause);
//		if (clause == null)
//			return Individual.create(getIRI("_r0")); 
			
		int index; 
		if (clause2index.containsKey(clause)) 
			index = clause2index.get(clause); 
		else {
			index = clause2index.size() + 1; 
			index2clause.put(index, clause);
			clause2index.put(clause, index); 
		}

		return Individual.create(getIRI("_r" + index));
	}

	private boolean queryEncoded = false; 
	protected LinkedList<long[]> addedData = new LinkedList<long[]>();
	
	public Collection<long[]> getAddedData() {
		return addedData; 
	}
	
	private void encodingQuery(QueryRecord[] botQuerRecords) {
		if (queryEncoded) return ; 
		queryEncoded = true;
		
		if (currentQuery.getArity() > 0 && currentQuery.getArity() < 3) {
			encodingAtomicQuery(botQuerRecords);

		} else {
			DLClause queryClause = currentQuery.getClause(); 
			Atom[] bodyAtoms = queryClause.getBodyAtoms(); 
			for (Atom bodyAtom: bodyAtoms) 
				addQueryRule(bodyAtom, bodyAtoms); 
		}
	}
	
	protected void addQueryRule(Atom atom, Atom[] atoms) {
		DLClause newClause; 
		Atom headAtom; 
		
		headAtom = Atom.create(
				getTrackingDLPredicate(atom.getDLPredicate()), 
				DLClauseHelper.getArguments(atom));
		newClause = DLClause.create(new Atom[] {headAtom}, atoms); 
		queryClauses.add(newClause);
	}

	public static final String trackingPredicateRelation = Namespace.PAGODA_AUX + "isTrackingPredicateFor"; 
	
	public static final String QueryPredicate = "http://www.example.org/Query"; 
	
	protected String getCurrentQueryPredicate() {
		return QueryPredicate + currentQuery.getQueryID(); 
	}

	protected void encodingAtomicQuery(QueryRecord[] botQuerRecords) {
		encodingAtomicQuery(botQuerRecords, false);
	}
	
	protected void encodingAtomicQuery(QueryRecord[] botQuerRecords, boolean includingBottom) {
		DLClause queryClause = currentQuery.getClause(); 
		AnswerTuples answerTuples = currentQuery.getGapAnswers(); 
		String[] answerVariables = currentQuery.getAnswerVariables(); 
		
		String currentQueryPredicate = getCurrentQueryPredicate();
		Atom newAtom; 
		if (answerVariables.length == 1) {
			AtomicConcept queryConcept = AtomicConcept.create(currentQueryPredicate);
			newAtom = Atom.create(queryConcept, Variable.create(answerVariables[0]));
		}
		else {
			AtomicRole queryRole = AtomicRole.create(currentQueryPredicate); 
			newAtom = Atom.create(queryRole, Variable.create(answerVariables[0]), Variable.create(answerVariables[1]));  
		}
		
		Atom[] bodyAtoms = queryClause.getBodyAtoms();
		Atom[] newBodyAtoms = new Atom[queryClause.getBodyLength() + 1]; 
		for (int i = 0; i < bodyAtoms.length; ++i)
			newBodyAtoms[i + 1] = bodyAtoms[i]; 
		newBodyAtoms[0] = newAtom;
		
		for (Atom bodyAtom: bodyAtoms) 
			addQueryRule(bodyAtom, newBodyAtoms);

		RDFoxTripleManager tripleManager = new RDFoxTripleManager(store.getDataStore(), true);//I don't think the triples need to be added incrementally
		MyPrefixes prefixes = MyPrefixes.PAGOdAPrefixes;
		long[] triple; 
		long predicate = tripleManager.getResourceID(AtomicConcept.create(currentQueryPredicate));   
		long rdftype = tripleManager.getResourceID(AtomicRole.create(Namespace.RDF_TYPE));
		if (answerVariables.length == 1) {		
			for (AnswerTuple answer; answerTuples.isValid(); answerTuples.moveNext()) {
				answer = answerTuples.getTuple();
				triple = new long[] { tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0))), rdftype, predicate }; 
				addedData.add(triple);
				tripleManager.addTripleByID(triple);
//				System.out.println("To be removed ... \n" + tripleManager.getRawTerm(tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0)))) + " " + tripleManager.getRawTerm(rdftype) + " " + tripleManager.getRawTerm(predicate)); 
			}
		}
		else {
			for (AnswerTuple answer; answerTuples.isValid(); answerTuples.moveNext()) {
				answer = answerTuples.getTuple();
				triple = new long[] { tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0))), predicate, tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(1))) }; 
				addedData.add(triple);
				tripleManager.addTripleByID(triple);
			}
		}
		answerTuples.dispose();

		if (includingBottom && botQuerRecords != null) {
			int index = 0; 
			for (QueryRecord  botQueryRecord: botQuerRecords) {
				answerTuples = botQueryRecord.getGapAnswers();
				int subID = 0;//botQueryRecord.getSubID(); 
				String p = subID == 0 ? AtomicConcept.NOTHING.getIRI() : Namespace.OWL_NS + "Nothing_final" + (++index); 
				predicate = tripleManager.getResourceID(AtomicConcept.create(p = getTrackingPredicate(p)));
				for (AnswerTuple answer; answerTuples.isValid(); answerTuples.moveNext()) {
					answer = answerTuples.getTuple(); 
//					System.out.println("To be remove ... " + answer.getRawTerm(0));
					triple = new long[] { tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0))), rdftype, predicate }; 
					addedData.add(triple);
					tripleManager.addTripleByID(triple);
				}
				answerTuples.dispose();
			}
		}
		
		Logger_MORe.logInfo(addedData.size() + " triples are added into the store.");
	}

	protected DLPredicate getGapDLPredicate(DLPredicate dlPredicate) {
		return getDLPredicate(dlPredicate, GapTupleIterator.gapPredicateSuffix); 
	}

	DLPredicate getDLPredicate(DLPredicate p, String suffix) {
		if (p instanceof AtomicConcept) 
			return AtomicConcept.create(((AtomicConcept) p).getIRI() + suffix);
		else if (p instanceof DatatypeRestriction) {
			DatatypeRestriction restriction = (DatatypeRestriction) p; 
			String newURI = restriction.getDatatypeURI() + suffix; 
			return getDatatypeRestriction(restriction, newURI);
		}
		else if (p instanceof AtomicRole)
			return AtomicRole.create(((AtomicRole) p).getIRI() + suffix);
		else if (p instanceof AnnotatedEquality || p instanceof Equality) 
			return AtomicRole.create(Namespace.EQUALITY + suffix);
		else if (p instanceof Inequality) 
			return AtomicRole.create(Namespace.INEQUALITY + suffix);
		else {
			Logger_MORe.logDebug("strange DL predicate appeared ... " + p, 
					"the program paused here in TrackingRuleEncoderDisj.java"); 
			return null;
		}
	}

	protected DLPredicate getTrackingDLPredicate(DLPredicate dlPredicate) {
		return getDLPredicate(dlPredicate, getTrackingSuffix(currentQuery.getQueryID())); 
	}
	
	protected static String getTrackingSuffix(String queryID) {
		return "_AUXt" + queryID; 
	}
	
	public String getTrackingPredicate(String predicateIRI) {
		if (predicateIRI.startsWith("<"))
			return predicateIRI.replace(">", getTrackingSuffix(currentQuery.getQueryID()) + ">");
		else 
			return predicateIRI + getTrackingSuffix(currentQuery.getQueryID());
	}

	protected DLPredicate getDatatypeRestriction(DatatypeRestriction restriction, String newName) {
		int length = restriction.getNumberOfFacetRestrictions(); 
		String[] facets = new String[length]; 
		Constant[] values = new Constant[length]; 
		for (int i = 0; i < length; ++i) {
			facets[i] = restriction.getFacetURI(i);
			values[i] = restriction.getFacetValue(i); 
		}
		return DatatypeRestriction.create(newName, facets, values); 
	}

	protected QueryRecord currentQuery;
	DLPredicate selected; 
	
	public void setCurrentQuery(QueryRecord record) {
		deprecateTrackingAndQueryRules();
		currentQuery = record;
		selected = AtomicConcept.create(getSelectedPredicate());
		trackingSuffix = "_AUXt" + currentQuery.getQueryID(); 
	}
	
	public void dispose() {
		deprecateTrackingAndQueryRules();
	}
	
	protected String getTrackingRuleText() {
		return DLClauseHelper.toString(trackingClauses);
	}
	
	protected String getQueryRuleText() {
		return DLClauseHelper.toString(queryClauses);
	}
	
	public String getTrackingProgram() {
		StringBuilder sb = getTrackingProgramBody();
		sb.insert(0, MyPrefixes.PAGOdAPrefixes.prefixesText()); 
		
//		///////
//		System.out.println("printing from TrackingRuleEncoder");
//		System.out.println(sb.toString());
//		///////
		
		return sb.toString(); 
	}
	
	protected StringBuilder getTrackingProgramBody() {
		encodingRules();
		encodingQuery(new QueryRecord[0]);

		StringBuilder sb = new StringBuilder(); 
		sb.append(getTrackingRuleText());
		sb.append(getEqualityRelatedRuleText());
		sb.append(getQueryRuleText());
		return sb; 
	}

	public void saveTrackingRules(String fileName) {
		BufferedWriter writer = null;
		try {
			writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(fileName)));
			writer.write(getTrackingProgram());
			writer.close();
		} catch (IOException e) {
			e.printStackTrace();
			return ;
		}
		Logger_MORe.logDebug("The tracking rules are saved in " + fileName + "."); 
	}

	private void deprecateTrackingAndQueryRules() {
		trackingClauses.clear(); 
		queryClauses.clear();
		addedData.clear();
		ruleEncoded = false; 
		queryEncoded = false; 
	}

	public String getSelectedPredicate() {
		return getIRI("_selected" + currentQuery.getQueryID()); 
	}

	public DLClause getSelectedClause(String iri) {
		int index = iri.lastIndexOf("_r") + 2;
		int ruleIndex = Integer.parseInt(iri.substring(index));
		return index2clause.get(ruleIndex);
	}
	
	/**
	 * SELECT ?X
	 * WHERE {
	 * 	?X <http://www.w3.org/1999/02/22-rdf-syntax-ns#:type> :_selected?
	 * }
	 */
	public String getSelectedSPARQLQuery() {
		StringBuilder builder = new StringBuilder(); 
		builder.append("SELECT ?X\nWHERE {\n?X <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "); 
		builder.append(selected.toString()).append("\n}");  
		return builder.toString(); 
	}

	public OWLOntology getOntology() {
		return program.getOntology(); 
	}

	public UpperDatalogProgram getProgram() {
		return program;
	}
	
	protected String trackingSuffix; 
	
	public String getOriginalPredicate(String p) {
		if (p.startsWith("<")) {
			if (!p.endsWith(trackingSuffix + ">")) return null;
		}
		else 
			if (!p.endsWith(trackingSuffix)) return null;
		
		return p.replace(trackingSuffix, ""); 
	}

	public boolean isAuxPredicate(String p) {
		return false; 
	}
	
	protected Set<String> unaryPredicates = new HashSet<String>(); 
	protected Set<String> binaryPredicates = new HashSet<String>();
	
}
