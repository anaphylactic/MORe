package uk.ac.ox.cs.pagoda.multistage.treatment;

import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.Variable;
import org.semanticweb.more.util.Logger_MORe;

import uk.ac.ox.cs.JRDFox.JRDFStoreException;
import uk.ac.ox.cs.JRDFox.store.TupleIterator;
import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.multistage.AnswerTupleID;
import uk.ac.ox.cs.pagoda.multistage.MultiStageQueryEngine;
import uk.ac.ox.cs.pagoda.multistage.MultiStageUpperProgram;
import uk.ac.ox.cs.pagoda.multistage.Violation;
import uk.ac.ox.cs.pagoda.query.AnswerTuple;
import uk.ac.ox.cs.pagoda.query.GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly;
import uk.ac.ox.cs.pagoda.util.SparqlHelper;

public class Treatment4Classification extends Pick4NegativeConceptNaive {
	
	public Treatment4Classification(MultiStageQueryEngine store, MultiStageUpperProgram multiProgram) {
		super(store, multiProgram);
	}
	
	public Set<AnswerTuple> makeSatisfiedAndReturnAddedTuples(Violation violation) {
		return makeSatisfiedAndReturnAddedTuples(violation, comp);
	}
	public void makeSatisfied(Violation violation, GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly gap) {
		makeSatisfied(violation, comp, gap);
	}	
		
	protected Set<AnswerTuple> makeSatisfiedAndReturnAddedTuples(Violation violation, Comparator<Atom> comp) {
		
		Set<AnswerTuple> ret = new HashSet<AnswerTuple>();
		
		LinkedList<AnswerTupleID> tuples = violation.getTuples();
		DLClause constraint = violation.getConstraint();
		Map<Variable, Integer> assignment = new HashMap<Variable, Integer>();
		
		if (constraint.getHeadLength() > 1) {
			Atom[] orderedAtoms = new Atom[constraint.getHeadLength()];
			int index = 0; 
			
			for (Atom headAtom: constraint.getHeadAtoms()) {
				orderedAtoms[index++] = headAtom;
			}
			
			Arrays.sort(orderedAtoms, comp);
	
			Set<AnswerTupleID> negTuples = new HashSet<AnswerTupleID>(); 
			String negativeQuery; 
			String[] subVars; 
			for (Atom headAtom: orderedAtoms) {
				negativeQuery = SparqlHelper.getSPARQLQuery(new Atom[] { MultiStageUpperProgram.getNegativeAtom(headAtom) }, 
						subVars = MultiStageUpperProgram.getVarSubset(violation.getVariables(), headAtom));
				negTuples.clear();
				Atom gapHeadAtom = addGap ? getGapAtom(headAtom) : null; 
				TupleIterator negAnswers = null; 
				try {
					negAnswers = engine.internal_evaluateNotExpanded(negativeQuery); 
					for (long multi = negAnswers.open(); multi != 0; multi = negAnswers.getNext()) 
						negTuples.add(new AnswerTupleID(negAnswers)); 
				} catch (JRDFStoreException e) {
					e.printStackTrace();
				} finally {
					if (negAnswers != null) negAnswers.dispose();
				}

				if (!tuples.isEmpty())
//					program.addUpdatedPredicates(dependencyGraph.getDependence(headAtom.getDLPredicate()));
					program.addUpdatedPredicate(headAtom.getDLPredicate());

				Comparator<AnswerTupleID> tComp = createTupleComparator(subVars); 
				Collections.sort(tuples, tComp);
				
				AnswerTupleID lastAdded = null; 
				
				for (Iterator<AnswerTupleID> iter = tuples.iterator(); iter.hasNext(); ) {
					
					AnswerTupleID tuple = iter.next(); 
					if (negTuples.contains(MultiStageUpperProgram.project(tuple, violation.getVariables(), subVars))) ;
					else {
						if (lastAdded == null || tComp.compare(lastAdded, tuple) != 0) {
							lastAdded = tuple; 
							tuple.getAssignment(violation.getVariables(), assignment);
							AnswerTuple t = addTripleByID(headAtom, gapHeadAtom, assignment);
							if (t != null)
								ret.add(t);
						}
						iter.remove();
					}
				}
//				tuples.reset();
				
//				if (tuples.isEmpty()) 
//					return ret; 
			}
			
			if (!tuples.isEmpty())
				Logger_MORe.logInfo("some tuples in this violation couldn't be fixed - this shouldn't be possible!");
//				return false; 
			
//			return ret;
			
		}
		else {
			
			Logger_MORe.logInfo("violation associated with a clause that is not disjunctive - this should not happen doing classification!");
			//place some logDebig here - should we ever get here if we are only dealing with 
			//disjunctive axioms outside JRDFox
			
			Set<Atom> headAtoms = new HashSet<Atom>(); 
			for (DLClause clause: program.convertExist(constraint, violation.getClause())) {
				if (DLClauseHelper.hasSubsetBodyAtoms(clause, constraint)) {
					Atom tHeadAtom = clause.getHeadAtom(0);
					Atom tGapHeadAtom = addGap ? getGapAtom(tHeadAtom) : null; 
					if (DLClauseHelper.isGround(tHeadAtom)) {
						if (!addedGroundAtoms.contains(tHeadAtom)) {
							program.addUpdatedPredicate(tHeadAtom.getDLPredicate());
							
							AnswerTuple t = addTripleByID(tHeadAtom, tGapHeadAtom, null);
							if (t != null)
								ret.add(t);
							
							addedGroundAtoms.add(tHeadAtom);
						}
					}
					else headAtoms.add(tHeadAtom); 
				}
				else {
					Logger_MORe.logError("There might be an error here... Can't happend!!!"); 
				}
			}
			if (!tuples.isEmpty())
				for (Atom atom: headAtoms)
					program.addUpdatedPredicate(atom.getDLPredicate()); 

			for (AnswerTupleID tuple: tuples) { 
				tuple.getAssignment(violation.getVariables(), assignment); 
				for (Atom atom: headAtoms) {
					AnswerTuple t = addTripleByID(atom, getGapAtom(atom), assignment);
					if (t != null)
						ret.add(t);
				}
			}
		}
		
		assignment.clear(); 
		return ret;
	}
	
	protected void makeSatisfied(Violation violation, Comparator<Atom> comp, GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly gap) {
		
		LinkedList<AnswerTupleID> tuples = violation.getTuples();
		DLClause constraint = violation.getConstraint();
		Map<Variable, Integer> assignment = new HashMap<Variable, Integer>();
		
		if (constraint.getHeadLength() > 1) {
			Atom[] orderedAtoms = new Atom[constraint.getHeadLength()];
			int index = 0; 
			
			for (Atom headAtom: constraint.getHeadAtoms()) {
				orderedAtoms[index++] = headAtom;
			}
			
			Arrays.sort(orderedAtoms, comp);
	
//			Set<AnswerTupleID> negTuples = new HashSet<AnswerTupleID>(); 
//			String negativeQuery; 
			String[] subVars; 
			for (Atom headAtom: orderedAtoms) {
				subVars = MultiStageUpperProgram.getVarSubset(violation.getVariables(), headAtom);
//				Atom negAtom = MultiStageUpperProgram.getNegativeAtom(headAtom);
//				negativeQuery = SparqlHelper.getSPARQLQuery(new Atom[] { negAtom }, 
//						subVars);
//				negTuples.clear();
//				TupleIterator negAnswers = null; 
//				try {
//					negAnswers = engine.internal_evaluateNotExpanded(negativeQuery); 
//					for (long multi = negAnswers.open(); multi != 0; multi = negAnswers.getNext()) 
//						negTuples.add(new AnswerTupleID(negAnswers)); 
//				} catch (JRDFStoreException e) {
//					e.printStackTrace();
//				} finally {
//					if (negAnswers != null) negAnswers.dispose();
//				}

				if (!tuples.isEmpty())
//					program.addUpdatedPredicates(dependencyGraph.getDependence(headAtom.getDLPredicate()));
					program.addUpdatedPredicate(headAtom.getDLPredicate());

				Comparator<AnswerTupleID> tComp = createTupleComparator(subVars); 
				Collections.sort(tuples, tComp);
				
				AnswerTupleID lastAdded = null; 
				
				Atom gapHeadAtom = addGap ? getGapAtom(headAtom) : null; 
				for (Iterator<AnswerTupleID> iter = tuples.iterator(); iter.hasNext(); ) {
					
					AnswerTupleID tuple = iter.next(); 
//					if (negTuples.contains(MultiStageUpperProgram.project(tuple, violation.getVariables(), subVars))) ;
//					else {
						if (lastAdded == null || tComp.compare(lastAdded, tuple) != 0) {
							lastAdded = tuple; 
							tuple.getAssignment(violation.getVariables(), assignment);
							AnswerTuple t = addTripleByID(headAtom, gapHeadAtom, assignment);
							if (t != null)
								gap.registerTuple(t);
//								ret.add(t);
						}
						iter.remove();
//					}
				}
//				tuples.reset();
				
//				if (tuples.isEmpty()) 
//					return ret; 
			}
			
			if (!tuples.isEmpty())
				Logger_MORe.logInfo("some tuples in this violation couldn't be fixed - this shouldn't be possible!");
//				return false; 
			
//			return ret;
			
		}
		else {
			
			Logger_MORe.logInfo("violation associated with a clause that is not disjunctive - this should not happen doing classification!");
			//place some logDebig here - should we ever get here if we are only dealing with 
			//disjunctive axioms outside JRDFox
			
			Set<Atom> headAtoms = new HashSet<Atom>(); 
			for (DLClause clause: program.convertExist(constraint, violation.getClause())) {
				if (DLClauseHelper.hasSubsetBodyAtoms(clause, constraint)) {
					Atom tHeadAtom = clause.getHeadAtom(0);
					Atom tGapHeadAtom = addGap ? getGapAtom(tHeadAtom) : null; 
					if (DLClauseHelper.isGround(tHeadAtom)) {
						if (!addedGroundAtoms.contains(tHeadAtom)) {
							program.addUpdatedPredicate(tHeadAtom.getDLPredicate());
							
							AnswerTuple t = addTripleByID(tHeadAtom, tGapHeadAtom, null);
							if (t != null)
								gap.registerTuple(t);
//								ret.add(t);
							
							addedGroundAtoms.add(tHeadAtom);
						}
					}
					else headAtoms.add(tHeadAtom); 
				}
				else {
					Logger_MORe.logError("There might be an error here... Can't happend!!!"); 
				}
			}
			if (!tuples.isEmpty())
				for (Atom atom: headAtoms)
					program.addUpdatedPredicate(atom.getDLPredicate()); 

			for (AnswerTupleID tuple: tuples) { 
				tuple.getAssignment(violation.getVariables(), assignment); 
				for (Atom atom: headAtoms) {
					AnswerTuple t = addTripleByID(atom, getGapAtom(atom), assignment);
					if (t != null)
						gap.registerTuple(t);
//						ret.add(t);
				}
			}
		}
		
		assignment.clear(); 
	}
}
