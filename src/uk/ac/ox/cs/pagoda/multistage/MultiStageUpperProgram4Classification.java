package uk.ac.ox.cs.pagoda.multistage;


import java.util.Collection;
import java.util.LinkedList;

import org.semanticweb.HermiT.model.AtLeast;
import org.semanticweb.HermiT.model.AtLeastConcept;
import org.semanticweb.HermiT.model.AtLeastDataRange;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicNegationConcept;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.more.pagoda.rules.OverApproxExist4Classification;

import uk.ac.ox.cs.pagoda.constraints.BottomStrategy;
import uk.ac.ox.cs.pagoda.rules.Approximator;
import uk.ac.ox.cs.pagoda.rules.OverApproxExist;
import uk.ac.ox.cs.pagoda.rules.Program;

public class MultiStageUpperProgram4Classification extends RestrictedApplication{

	String outputPath;
	
	
	public MultiStageUpperProgram4Classification(Program program, BottomStrategy upperBottom) {
		super(program, upperBottom);
		
		 outputPath = program.getDirectory() + "multi.dlog";
		save(outputPath);
	}

	public String getOutputPath(){
		return outputPath;
	}
	
	@Override
	protected void completeInit(){
		for (DLClause clause : ((OverApproxExist4Classification) m_approxExist).getAuxiliaryClauses())
			addDatalogRule(clause);
		
		super.completeInit();
	}
	
	@Override
	protected Approximator initApproximator(){
		return new OverApproxExist4Classification();
	}
	
	@Override
	protected void preprocessClause(DLClause clause, Collection<DLClause> introducedConstraints){
		//we need to preprocess clauses differently because we don't want to treat as constraints rules 
		//that only have one existential restriction in the head
		if (m_bottom.isBottomRule(clause) || clause.getHeadLength() == 1 && !(clause.getHeadAtom(0).getDLPredicate() instanceof AtLeast)) 
			addDatalogRule(clause);				
		else if (clause.getHeadLength() == 1 && clause.getHeadAtom(0).getDLPredicate() instanceof AtLeast){
			Atom atom = clause.getHeadAtom(0);
			if (atom.getDLPredicate() instanceof AtLeastConcept) {
				AtLeastConcept atLeast = (AtLeastConcept) atom.getDLPredicate(); 
				if (atLeast.getToConcept() instanceof AtomicNegationConcept) {
					AtomicConcept positive = ((AtomicNegationConcept) atLeast.getToConcept()).getNegatedAtomicConcept(); 
					AtomicConcept negative = OverApproxExist.getNegationConcept(positive); 
					Atom atom1 = Atom.create(positive, X);
					Atom atom2 = Atom.create(negative, X);
					introducedConstraints.add(DLClause.create(new Atom[0], new Atom[] {atom1, atom2})); 

					Atom[] headAtom = new Atom[]{Atom.create(
							AtLeastConcept.create(atLeast.getArity(), atLeast.getOnRole(), negative), 
							atom.getArgument(0))};

					DLClause newClause = DLClause.create(headAtom, clause.getBodyAtoms()); 
					//				map.put(newClause, clause); //not necessary, this is only needed for constraints
					addDatalogRule(newClause); 
				}
				else if (!(atom.getDLPredicate() instanceof AtLeastDataRange))
					addDatalogRule(clause);
			}
		}
		else{
			LinkedList<Atom> newHeadAtoms = new LinkedList<Atom>(); 
			boolean changed = false; 
			for (Atom atom: clause.getHeadAtoms()) {
				if (atom.getDLPredicate() instanceof AtLeastConcept) {
					AtLeastConcept atLeast = (AtLeastConcept) atom.getDLPredicate(); 
					if (atLeast.getToConcept() instanceof AtomicNegationConcept) {
						AtomicConcept positive = ((AtomicNegationConcept) atLeast.getToConcept()).getNegatedAtomicConcept(); 
						AtomicConcept negative = OverApproxExist.getNegationConcept(positive); 
						Atom atom1 = Atom.create(positive, X);
						Atom atom2 = Atom.create(negative, X);
						introducedConstraints.add(DLClause.create(new Atom[0], new Atom[] {atom1, atom2})); 
						newHeadAtoms.add( 
								Atom.create(
										AtLeastConcept.create(atLeast.getArity(), atLeast.getOnRole(), negative), 
										atom.getArgument(0)));
						changed = true; 
						continue; 
					}
				}
				else if (atom.getDLPredicate() instanceof AtLeastDataRange)
					changed = true; 
				else 
					newHeadAtoms.add(atom);
				
			}
			if (!changed) constraints.add(clause);
			else if (!newHeadAtoms.isEmpty()) {
				DLClause newClause = DLClause.create(newHeadAtoms.toArray(new Atom[0]), clause.getBodyAtoms()); 
				map.put(newClause, clause); 
				constraints.add(newClause); 
			}
		}
	}
	
	@Override
	protected void addDatalogRule(DLClause clause) {
		for (DLClause cls : m_approxExist.convert(clause, clause))
			super.addDatalogRule(cls);	
	}

}
