package uk.ac.ox.cs.pagoda.tracking;
import java.util.LinkedList;

import org.semanticweb.HermiT.model.AtLeastConcept;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.more.pagoda.rules.UpperDatalogProgram4Classification;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.more.util.Utility;

import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.multistage.Normalisation;
import uk.ac.ox.cs.pagoda.query.AnswerTuple;
import uk.ac.ox.cs.pagoda.query.AnswerTuples;
import uk.ac.ox.cs.pagoda.query.ClassificationQueryType;
import uk.ac.ox.cs.pagoda.query.MultiQueryRecord;
import uk.ac.ox.cs.pagoda.query.QueryRecord4Classification;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.reasoner.light.RDFoxTripleManager;
import uk.ac.ox.cs.pagoda.rules.UpperDatalogProgram;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Namespace;


public class TrackingRuleEncoderDisjVar14Classification extends
		TrackingRuleEncoderDisjVar1 implements
		TrackingRuleEncoder4Classification {

	
	String trackingProgramOutPutPath;
	
	public TrackingRuleEncoderDisjVar14Classification(UpperDatalogProgram program, BasicQueryEngine store) {
		super(program, store);
		selected = AtomicConcept.create(getSelectedPredicate());
		trackingSuffix = "_AUXt";
		
		trackingProgramOutPutPath = program.getDirectory() + "tracking.dlog";
		saveTrackingRules(trackingProgramOutPutPath);
		
	}
	
	@Override
	public String getTrackingProgramOutputPath() {
		return trackingProgramOutPutPath;
	}

	@Override
	public void encodeClassificationQueries(MultiQueryRecord multiRecord) {
		for (QueryRecord4Classification query : multiRecord.getIndividualQueryRecords()){
			//just add to the store the tracking counterpart of the gap triples we want to track
			AnswerTuples answerTuples = query.getGapAnswers();
			RDFoxTripleManager tripleManager = new RDFoxTripleManager(store.getDataStore(), false);
			MyPrefixes prefixes = MyPrefixes.PAGOdAPrefixes;
			long[] triple; 
			long predicate;
			long individual;
			long rdftype = tripleManager.getResourceID(AtomicRole.create(Namespace.RDF_TYPE));
			for (AnswerTuple answer; answerTuples.isValid(); answerTuples.moveNext()) {
				answer = answerTuples.getTuple();
				if (query.getQueryType() == ClassificationQueryType.INDIVIDUAL){
					predicate = tripleManager.getResourceID(Utility.removeAngleBrackets(getTrackingPredicate(prefixes.expandIRI(answer.getRawTerm(0)))));
					individual = tripleManager.getResourceID(Utility.removeAngleBrackets(query.getQueryEntity()));
				}
				else{
					predicate = tripleManager.getResourceID(Utility.removeAngleBrackets(getTrackingPredicate(query.getQueryEntity())));
					individual = tripleManager.getResourceID(prefixes.expandIRI(Utility.removeAngleBrackets(answer.getRawTerm(0)))); 
				}
				triple = new long[] { individual, rdftype, predicate };
				addedData.add(triple);
				tripleManager.addTripleByID(triple);
				//					System.out.println("To be removed ... \n" + tripleManager.getRawTerm(tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0)))) + " " + tripleManager.getRawTerm(rdftype) + " " + tripleManager.getRawTerm(predicate)); 
			}
			answerTuples.dispose();
		}

//		Logger_MORe.logInfo(new HashSet<int[]>(addedData).size() + " triples are added into the store.");
		
//		///
//		RDFoxTripleManager tripleManager = new RDFoxTripleManager(store.getDataStore(), false);
//		for (int[] triple : addedData)
//			System.out.println(tripleManager.getRawTerm(triple[0]) + tripleManager.getRawTerm(triple[1]) + tripleManager.getRawTerm(triple[2]));
//		///
	}
//	@Override
//	public void encodingClassificationQuery(QueryRecord query) {
//		DLClause queryClause = query.getClause(); 
//		AnswerTuples answerTuples = query.getGapAnswers(); 
//		String[] answerVariables = query.getAnswerVariables(); 
//		
//		String queryPredicate = QueryPredicate + query.getQueryID(); 
//		Atom newAtom; 
//		if (answerVariables.length == 1) {
//			AtomicConcept queryConcept = AtomicConcept.create(queryPredicate);
//			newAtom = Atom.create(queryConcept, Variable.create(answerVariables[0]));
//		}
//		else {
//			AtomicRole queryRole = AtomicRole.create(queryPredicate); 
//			newAtom = Atom.create(queryRole, Variable.create(answerVariables[0]), Variable.create(answerVariables[1]));  
//		}
//		
//		Atom[] bodyAtoms = queryClause.getBodyAtoms();
//		Atom[] newBodyAtoms = new Atom[queryClause.getBodyLength() + 1]; 
//		for (int i = 0; i < bodyAtoms.length; ++i)
//			newBodyAtoms[i + 1] = bodyAtoms[i]; 
//		newBodyAtoms[0] = newAtom;
//		
//		for (Atom bodyAtom: bodyAtoms) 
//			addQueryRule(bodyAtom, newBodyAtoms);
//
//		RDFoxTripleManager tripleManager = new RDFoxTripleManager(store.getDataStore(), false);
//		MyPrefixes prefixes = MyPrefixes.PAGOdAPrefixes;
//		int[] triple; 
//		int predicate = tripleManager.getResourceID(AtomicConcept.create(queryPredicate));   
//		int rdftype = tripleManager.getResourceID(AtomicRole.create(Namespace.RDF_TYPE));
//		if (answerVariables.length == 1) {		
//			for (AnswerTuple answer; answerTuples.isValid(); answerTuples.moveNext()) {
//				answer = answerTuples.getTuple();
//				triple = new int[] { tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0))), rdftype, predicate }; 
//				addedData.add(triple);
//				tripleManager.addTripleByID(triple);
////				System.out.println("To be removed ... \n" + tripleManager.getRawTerm(tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0)))) + " " + tripleManager.getRawTerm(rdftype) + " " + tripleManager.getRawTerm(predicate)); 
//			}
//		}
//		else {
//			for (AnswerTuple answer; answerTuples.isValid(); answerTuples.moveNext()) {
//				answer = answerTuples.getTuple();
//				triple = new int[] { tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(0))), predicate, tripleManager.getResourceID(prefixes.expandIRI(answer.getRawTerm(1))) }; 
//				addedData.add(triple);
//				tripleManager.addTripleByID(triple);
//			}
//		}
//		answerTuples.dispose();
//
//		Logger_MORe.logInfo(addedData.size() + " triples are added into the store.");
//	}
	
	@Override
	public void encodingAuxiliaryRule(DLClause clause) {
		LinkedList<Atom> newHeadAtoms = new LinkedList<Atom>();
//		newHeadAtoms.add(Atom.create(selected, getIndividual4GeneralRule(clause)));//this is the only difference wrt method encodingRule(DLClause) 
		
		Atom headAtom;
		for (Atom atom: clause.getBodyAtoms()) {
			headAtom = Atom.create(
					getTrackingDLPredicate(atom.getDLPredicate()), 
					DLClauseHelper.getArguments(atom));
			newHeadAtoms.add(headAtom);
		}

		DLClause newClause;
		
		int offset = (clause.getBodyLength() == 1 && clause.getBodyAtom(0).getDLPredicate().toString().contains("owl:Nothing")) ? 1 : 2; 
		
		Atom[] newBodyAtoms = new Atom[clause.getBodyLength() + offset];
		headAtom = clause.getHeadAtom(0);
		newBodyAtoms[0] = Atom.create(
				getTrackingDLPredicate(headAtom.getDLPredicate()), 
				DLClauseHelper.getArguments(headAtom));
		
		if (offset == 2)
		newBodyAtoms[1] = Atom.create(
				getGapDLPredicate(headAtom.getDLPredicate()), 
				DLClauseHelper.getArguments(headAtom));

		for (int i = 0; i < clause.getBodyLength(); ++i)
			newBodyAtoms[i + offset] = clause.getBodyAtom(i); 
		
		for (Atom atom: newHeadAtoms) {
			newClause = DLClause.create(new Atom[] {atom}, newBodyAtoms); 
			trackingClauses.add(newClause);
		}
	}
	
	@Override
	public boolean encodingRules() {
		if (super.encodingRules()){
			for (DLClause clause : ((UpperDatalogProgram4Classification) program).getAuxiliaryClauses())
				encodingAuxiliaryRule(clause);
			return true;
		}
		else
			return false;
	}
	
	protected DLPredicate getTrackingDLPredicate(DLPredicate dlPredicate) {
		return getDLPredicate(dlPredicate, getTrackingSuffix("")); 
	}
	public String getTrackingPredicate(String predicateIRI) {
		if (predicateIRI.startsWith("<"))
			return predicateIRI.replace(">", getTrackingSuffix("") + ">");
		else 
			return predicateIRI + getTrackingSuffix("");
	}
	public String getSelectedPredicate() {
		return getIRI("_selected"); 
	}
	
	@Override
	protected StringBuilder getTrackingProgramBody() {
		encodingRules();
//		encodingQuery(new QueryRecord[0]);

		StringBuilder sb = new StringBuilder(); 
		sb.append(getTrackingRuleText());
		if (program.containsEquality()){
			sb.append(getEqualityRelatedRuleText());
			Logger_MORe.logDebug("# adding tracking rules for EQUALITY");
		}
		sb.append(getQueryRuleText());
		return sb; 
	}
	
	////
	@Override 
	protected boolean isCurrentQueryBottom(){
		return false;
	}
	
	@Override
	protected DLPredicate getAuxPredicate(DLPredicate p) {
		if (p instanceof AtLeastConcept) {
			StringBuilder builder = new StringBuilder(
					Normalisation.getAuxiliaryConcept4Disjunct((AtLeastConcept) p));
			builder.append("_AUXa");//.append(currentQuery.getQueryID()); 
			return AtomicConcept.create(builder.toString()); 
		}
		
		return getDLPredicate(p, "_AUXa");// + currentQuery.getQueryID());
	}
	
	@Override 
	protected DLPredicate generateAuxiliaryRule(AtomicRole p) {
//		if (currentQuery.isBottom()) 
//			return getTrackingDLPredicate(p);
		
		DLPredicate ret = getAuxPredicate(p); 
		Atom[] headAtom = new Atom[] {Atom.create(ret, X, Y)};

		addTrackingClause(
				DLClause.create(headAtom, new Atom[] {Atom.create(getTrackingDLPredicate(p), X, Y)})); 
		addTrackingClause(
				DLClause.create(headAtom, new Atom[] {Atom.create(getTrackingBottomDLPredicate(p), X, Y)})); 
		
		return ret; 
	}

	
	@Override
	protected DLPredicate generateAuxiliaryRule(AtomicConcept p) {
//		if (currentQuery.isBottom())
//			return getTrackingDLPredicate(p);  
		
		DLPredicate ret = getAuxPredicate(p); 
		Atom[] headAtom = new Atom[] {Atom.create(ret, X)}; 
		addTrackingClause(
				DLClause.create(headAtom, 
						new Atom[] { Atom.create(getTrackingDLPredicate(p), X)})); 
		addTrackingClause(
				DLClause.create(headAtom, 
						new Atom[] { Atom.create(getTrackingBottomDLPredicate(p), X)}));
		
		return ret; 
	}
	@Override
	public String getTrackingProgram() {
		StringBuilder sb = getTrackingProgramBody();
		sb.insert(0, MyPrefixes.PAGOdAPrefixes.prefixesText()); 
		return sb.toString(); 
	}

	
	
	////
}
