package uk.ac.ox.cs.pagoda.query;

import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.Variable;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.rules.GeneralProgram;
import uk.ac.ox.cs.pagoda.tracking.TrackingRuleEncoder;
import uk.ac.ox.cs.pagoda.util.ConjunctiveQueryHelper;
import uk.ac.ox.cs.pagoda.util.Namespace;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;

public class QueryRecord {
	
	public static final String botQueryText = "SELECT ?X\nWHERE {\n?X <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Nothing>\n}";

	protected Step diffculty;
	
	protected String queryText; 
	protected int queryID = -1; 
	protected String[] answerVariables = null;
	protected Set<AnswerTuple> soundAnswerTuples = new HashSet<AnswerTuple>(); 
	protected Set<AnswerTuple> gapAnswerTuples = null;
	
	protected QueryManager m_manager; 
	
	public QueryRecord(QueryManager manager, String text, int id, int subID) {
		m_manager =manager; 
		resetInfo(text, id, subID);
		resetTimer(); 
	}
	
	public void resetInfo(String text, int id, int subid) {
		queryID = id;
		subID = subid; 
		stringQueryID = id + (subID == 0 ? "" : "_" + subID);
		m_manager.remove(queryText); 
		m_manager.put(text, this); 
		queryText = text; 
		queryClause = null; 
		answerVariables = ConjunctiveQueryHelper.getAnswerVariables(queryText);
	}

	public void resetTimer() {
		int length = Step.values().length; 
		timer = new double[length]; 
		for (int i = 0; i < length; ++i) timer[i] = 0; 
	}
	
	public AnswerTuples getAnswers() {
		if (processed())
			return getLowerBoundAnswers();
		
		return getUpperBoundAnswers(); 
	}
	
	
	public AnswerTuples getLowerBoundAnswers() {
		return new AnswerTuplesImp(answerVariables, soundAnswerTuples); 
	}
	
	public AnswerTuples getUpperBoundAnswers() {
		return new AnswerTuplesImp(answerVariables, soundAnswerTuples, gapAnswerTuples); 
	}
	
	public boolean updateLowerBoundAnswers(AnswerTuples answerTuples) {
		if (answerTuples == null) return false; 			
		boolean update = false;
		for (AnswerTuple tuple; answerTuples.isValid(); answerTuples.moveNext()) {
			tuple = answerTuples.getTuple();
			if (!soundAnswerTuples.contains(tuple) && (gapAnswerTuples == null || gapAnswerTuples.contains(tuple))) {
				soundAnswerTuples.add(tuple);
				if (gapAnswerTuples != null)
					gapAnswerTuples.remove(tuple);
				update = true; 
			}
		}
		Logger_MORe.logTrace("The number of answers in the lower bound: " + soundAnswerTuples.size()); 

		return update; 
	}
	
	public boolean updateUpperBoundAnswers(AnswerTuples answerTuples) {
		return updateUpperBoundAnswers(answerTuples, false); 
	}
	
	public boolean updateUpperBoundAnswers(AnswerTuples answerTuples, boolean toCheckAux) {
		Set<AnswerTuple> tupleSet = new HashSet<AnswerTuple>();
		String str; 
		AnswerTuple tuple;
		for (; answerTuples.isValid(); answerTuples.moveNext()) {
			tuple = answerTuples.getTuple();
			str = tuple.toString(); 
			if ((isBottom() || !str.contains(Namespace.PAGODA_ANONY)) && (!toCheckAux || !containsAuxPredicate(str)) && !soundAnswerTuples.contains(tuple))
				tupleSet.add(tuple);
		}
	
		if (gapAnswerTuples == null) {
			gapAnswerTuples = tupleSet; 
			
			Logger_MORe.logTrace("The number of answers in the upper bound: " + (soundAnswerTuples.size() + gapAnswerTuples.size()));
			return true; 
		}
		
		boolean update = false; 
		for (Iterator<AnswerTuple> iter = gapAnswerTuples.iterator(); iter.hasNext(); ) {
			tuple = iter.next(); 
			if (!tupleSet.contains(tuple)) {
				iter.remove(); 
				update = true; 
			}
		}
		
		Logger_MORe.logDebug("The number of answers in the upper bound: " + (soundAnswerTuples.size() + gapAnswerTuples.size()));
		
		return update; 
	}
	
	public boolean updateUpperBoundAnswers(Collection<AnswerTuple> answers) {
		AnswerTuples answerTuples = new AnswerTuplesImp(answerVariables, new HashSet<AnswerTuple>(answers));
		return updateUpperBoundAnswers(answerTuples);
	}
	
	
	protected boolean containsAuxPredicate(String str) {
		return  str.contains(Namespace.PAGODA_AUX) || str.contains("_AUX") || 
				str.contains(TrackingRuleEncoder.QueryPredicate) || str.contains("owl#Nothing") ||
				str.contains("internal:def"); 
	}

	boolean processed = false; 

	public void markAsProcessed() {
		processed = true; 
	}

	public boolean processed() {
		if (gapAnswerTuples != null && gapAnswerTuples.isEmpty()) processed = true; 
		return processed; 
	}

	public String[] getAnswerVariables() {
		return answerVariables; 
	}
	
	public String getQueryText() {
		return queryText; 
	}
	
	String stringQueryID = null; 
	
	public String getQueryID() {
		return stringQueryID; 
	}
	
	public AnswerTuples getGapAnswers() {
		return new AnswerTuplesImp(answerVariables, gapAnswerTuples); 
	}

	public String toString() {
		return queryText; 
	}
	
	public static final String SEPARATOR = "----------------------------------------"; 

	public void outputAnswers(boolean outputTuples) {
		
		int answerCounter = soundAnswerTuples.size(); 
		if (!processed()) answerCounter += gapAnswerTuples.size(); 
		
		if (outputTuples) {
			StringBuilder tuples = new StringBuilder(); 
			tuples.append("The number of answer tuples: ").append(answerCounter).append(Utility_PAGOdA.LINE_SEPARATOR);
			StringBuilder space = new StringBuilder(); 
			int arity = getArity(), varSpace = 0; 
			for (int i = 0; i < arity; ++i)
				varSpace += answerVariables[i].length(); 
			for (int i = 0; i < (SEPARATOR.length() - varSpace) / (arity + 1); ++i)
				space.append(" "); 
			for (int i = 0; i < getArity(); ++i) {
				tuples.append(space).append(answerVariables[i]); 
			}
			tuples.append(Utility_PAGOdA.LINE_SEPARATOR).append(SEPARATOR).append(Utility_PAGOdA.LINE_SEPARATOR); 
			tuples.append(outputSoundAnswerTuple());
			if (!processed())
				tuples.append(outputGapAnswerTuple());
			tuples.append(SEPARATOR);

			Logger_MORe.logInfo(tuples.toString()); 
		}
		else 
			Logger_MORe.logInfo("The number of answer tuples: " + answerCounter); 
		
	}
	
	public void outputTimes() {
		for (Step step: Step.values()) {
			Logger_MORe.logDebug("time for " + step + ": " + timer[step.ordinal()]); 
		}
	}
	
	public String outputSoundAnswerTuple() {
		StringBuilder builder = new StringBuilder(); 
		for (AnswerTuple tuple: soundAnswerTuples)
			builder.append(tuple.toString()).append(Utility_PAGOdA.LINE_SEPARATOR);
		return builder.toString(); 
	}
	
	public String outputGapAnswerTuple() {
		StringBuilder builder = new StringBuilder(); 
		for (AnswerTuple tuple: gapAnswerTuples)
			builder.append(tuple.toString()).append(Utility_PAGOdA.LINE_SEPARATOR);
		return builder.toString(); 
	}
	
	public void setDifficulty(Step step) {
		this.diffculty = step;   
	}

	public Step getDifficulty() {
		return diffculty; 
	}

	OWLOntology relevantOntology = null; 
	Set<DLClause> relevantClauses = new HashSet<DLClause>(); 

	public void setRelevantOntology(OWLOntology knowledgebase) {
		relevantOntology = knowledgebase; 
	}
	
	public OWLOntology getRelevantOntology() {
		return relevantOntology; 
	}

	public void saveRelevantOntology(String filename) {
		if (relevantOntology == null) return ; 
		OWLOntologyManager manager = relevantOntology.getOWLOntologyManager(); 
		try {
			FileOutputStream outputStream = new FileOutputStream(filename); 
			manager.saveOntology(relevantOntology, outputStream);
			outputStream.close();
		} catch (OWLOntologyStorageException e) {
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void saveRelevantClause() {
		if (relevantClauses == null) return ; 
		GeneralProgram p = new GeneralProgram(relevantClauses, relevantOntology);
		p.save();
	}


	public void removeUpperBoundAnswers(Collection<AnswerTuple> answers) {
		for (AnswerTuple answer: answers) {
			if (soundAnswerTuples.contains(answer))
				Logger_MORe.logError("The answer (" + answer + ") cannot be removed, because it is in the lower bound.");
			if (!gapAnswerTuples.contains(answer))
				Logger_MORe.logError("The answer (" + answer + ") cannot be removed, because it is not in the upper bound.");
			gapAnswerTuples.remove(answer);
		}
	}


	public void addLowerBoundAnswers(Collection<AnswerTuple> answers) {
		for (AnswerTuple answer: answers) {
			if (soundAnswerTuples.contains(answer))
				Logger_MORe.logError("The answer (" + answer + ") cannot be added, because it is in the lower bound.");
			if (!gapAnswerTuples.contains(answer))
				Logger_MORe.logError("The answer (" + answer + ") cannot be added, because it is not in the upper bound.");
			
			soundAnswerTuples.add(answer); 
			gapAnswerTuples.remove(answer);
		}
	}
	
	public int getNoOfSoundAnswers() {
		return soundAnswerTuples.size(); 
	}
	
	public enum Step {LowerBound, UpperBound, ELLowerBound, 
		Fragment, FragmentRefinement, Summarisation, Dependency, FullReasoning};  
	
	double[] timer; 

	public void addProcessingTime(Step step, double time) {
		timer[step.ordinal()] += time; 
	}

	public int getArity() {
		return answerVariables.length;
	}
	
	public static Collection<String> collectQueryTexts(Collection<QueryRecord> queryRecords) {
		Collection<String> texts = new LinkedList<String>(); 
		for (QueryRecord record: queryRecords)
			texts.add(record.queryText); 
		return texts;
	}

	public void addRelevantClauses(DLClause clause) {
		relevantClauses.add(clause);		
	}
	
	public Set<DLClause> getRelevantClauses() {
		return relevantClauses; 
	}

	public void clearClauses() {
		relevantClauses.clear();
	}

	public boolean isHorn() {
		for (DLClause clause: relevantClauses)
			if (clause.getHeadLength() > 1)
				return false;
		return true; 
	}

	public void saveABoxInTurtle(String filename) {
		try {
			BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(filename)));
			OWLIndividual a, b;
			StringBuilder builder = new StringBuilder(); 
			for (OWLAxiom axiom: relevantOntology.getABoxAxioms(true)) {
				if (axiom instanceof OWLClassAssertionAxiom) {
					OWLClassAssertionAxiom classAssertion = (OWLClassAssertionAxiom) axiom; 
					OWLClass c = (OWLClass) classAssertion.getClassExpression(); 
					a = classAssertion.getIndividual();
					builder.append(a.toString()).append(" <").append(Namespace.RDF_TYPE).append("> ").append(c.toString()); 
				}
				else if (axiom instanceof OWLObjectPropertyAssertionAxiom) {
					OWLObjectPropertyAssertionAxiom propertyAssertion = (OWLObjectPropertyAssertionAxiom) axiom; 
					OWLObjectProperty p = (OWLObjectProperty) propertyAssertion.getProperty(); 
					a = propertyAssertion.getSubject(); 
					b = propertyAssertion.getObject(); 
					builder.append(a.toString()).append(" ").append(p.toString()).append(" ").append(b.toString()); 
				}
				else if (axiom instanceof OWLDataPropertyAssertionAxiom) {
					OWLDataPropertyAssertionAxiom propertyAssertion = (OWLDataPropertyAssertionAxiom) axiom; 
					OWLDataProperty p = (OWLDataProperty) propertyAssertion.getProperty(); 
					a = propertyAssertion.getSubject(); 
					OWLLiteral l = propertyAssertion.getObject(); 
					builder.append(a.toString()).append(" ").append(p.toString()).append(" ").append(l.toString()); 
				}
				
				writer.write(builder.toString());
				writer.write(" .");
				writer.newLine();
				builder.setLength(0);
			}
			writer.close();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			
		}
	}

	int subID; 
	
	public void updateSubID() {
		++subID; 
		stringQueryID = String.valueOf(queryID) + "_" + subID;
	}
	
	DLClause queryClause = null; 

	public DLClause getClause() {
		if (queryClause != null)
			return queryClause; 
		return queryClause = DLClauseHelper.getQuery(queryText, null); 
	}

	public boolean isBottom() {
		return queryID == 0;
	}

	public int getNoOfCompleteAnswers() {
		return soundAnswerTuples.size() + gapAnswerTuples.size();
	}
	
	public int getSubID() {
		return subID; 
	}
	
	public boolean hasSameGapAnswers(QueryRecord that) {
		return gapAnswerTuples.containsAll(that.gapAnswerTuples) && that.gapAnswerTuples.containsAll(gapAnswerTuples); 
	}

	public void dispose() {
		m_manager.remove(queryText); 
		if (gapAnswerTuples != null) gapAnswerTuples.clear();
		if (soundAnswerTuples != null) soundAnswerTuples.clear();
		if (relevantClauses != null) relevantClauses.clear();
		if (relevantOntology != null)
			relevantOntology.getOWLOntologyManager().removeOntology(relevantOntology);
		answerVariables = null;
	}

	public boolean canBeEncodedIntoAtom() {
		// FIXME 
		return true; 
//		return false;
	}
	
	public boolean isPredicate(AnswerTuple a, int i) {
		Atom[] atoms = getClause().getBodyAtoms(); 
		Variable v = Variable.create(answerVariables[i]); 
		String iri; 
		for (Atom atom: atoms) { 
			DLPredicate p = atom.getDLPredicate();
			if (p instanceof AtomicConcept) {
				if (((AtomicConcept) p).getIRI().equals(v.toString())) return true; 
			}
			else if (p instanceof AtomicRole) {
				iri = ((AtomicRole) p).getIRI(); 
				if (iri.equals(v.toString())) return true;
				if (iri.startsWith("?")) 
					iri = a.getValue(iri.substring(1), answerVariables); 
				if (iri.equals(Namespace.RDF_TYPE) && atom.getArgument(1).equals(v)) return true; 
			}
		}
		return false;
	}

	public Set<AnswerTuple> getSoundAnswerTuples() {
		return soundAnswerTuples;
	}
	
	public Set<AnswerTuple> getGapAnswerTuples() {
		return gapAnswerTuples;
	}
	
}
