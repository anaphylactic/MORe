package uk.ac.ox.cs.pagoda.tracking;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.semanticweb.HermiT.model.AnnotatedEquality;
import org.semanticweb.HermiT.model.AtLeastConcept;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicNegationConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.Equality;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.model.Inequality;
import org.semanticweb.HermiT.model.InverseRole;
import org.semanticweb.HermiT.model.Term;
import org.semanticweb.HermiT.model.Variable;

import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.multistage.Normalisation;
import uk.ac.ox.cs.pagoda.reasoner.light.BasicQueryEngine;
import uk.ac.ox.cs.pagoda.rules.OverApproxExist;
import uk.ac.ox.cs.pagoda.rules.UpperDatalogProgram;
import uk.ac.ox.cs.pagoda.util.Namespace;

public class TrackingRuleEncoderDisjVar1 extends TrackingRuleEncoderWithGap {

	public TrackingRuleEncoderDisjVar1(UpperDatalogProgram program, BasicQueryEngine store) {
		super(program, store);
	}
	
	private Set<DLClause> disjunctiveRules = new HashSet<DLClause>();

	@Override
	public boolean encodingRules() {
		if (super.encodingRules()) {
			processDisjunctiveRules();
			return true; 
		}
		return false; 
	}
	
	protected boolean isCurrentQueryBottom(){
		return currentQuery.isBottom();
	}
	
	@Override
	protected void encodingRule(DLClause clause) {
		if (isCurrentQueryBottom()) {
//			super.encodingRule(clause);
			encodingBottomQueryClause(clause); 
			return ; 
		}
		
		DLClause original = program.getCorrespondingClause(clause);
		if (original.getHeadLength() <= 1) {
			super.encodingRule(clause);
		} 
		else {
			if (!DLClauseHelper.hasSubsetBodyAtoms(clause, original))
				super.encodingRule(clause);
			addDisjunctiveRule(original);
		}
			
	}
	

	private void processDisjunctiveRules() {
		for (DLClause clause: disjunctiveRules)
			encodingDisjunctiveRule(clause);
	}
	
	private Atom getAuxiliaryAtom(Atom headAtom) {
		DLPredicate p = headAtom.getDLPredicate(); 
		if (p instanceof AtLeastConcept) {
			return Atom.create(generateAuxiliaryRule((AtLeastConcept) p, true), headAtom.getArgument(0)); 
		}
		if (p instanceof AtomicConcept) 
			return Atom.create(generateAuxiliaryRule((AtomicConcept) p), headAtom.getArgument(0)); 
		if (p instanceof AtomicRole) 
			return Atom.create(generateAuxiliaryRule((AtomicRole) p), headAtom.getArgument(0), headAtom.getArgument(1));
		if (p instanceof Equality || p instanceof AnnotatedEquality) 
			return Atom.create(generateAuxiliaryRule(Equality.INSTANCE), headAtom.getArgument(0), headAtom.getArgument(1)); 
		if (p instanceof Inequality) 
			return Atom.create(generateAuxiliaryRule((Inequality) p), headAtom.getArgument(0), headAtom.getArgument(1)); 

		return null;
	}

	private Atom getTrackingAtom(Atom headAtom) {
		DLPredicate p = headAtom.getDLPredicate(); 
		if (p instanceof AtLeastConcept) {
			return Atom.create(getTrackingDLPredicate(AtomicConcept.create(Normalisation.getAuxiliaryConcept4Disjunct((AtLeastConcept) p))), headAtom.getArgument(0)); 
		}
		if (p instanceof AtomicConcept) 
			return Atom.create(getTrackingDLPredicate((AtomicConcept) p), headAtom.getArgument(0)); 
		if (p instanceof AtomicRole) 
			return Atom.create(getTrackingDLPredicate((AtomicRole) p), headAtom.getArgument(0), headAtom.getArgument(1));
		if (p instanceof Equality || p instanceof AnnotatedEquality) 
			return Atom.create(getTrackingDLPredicate(Equality.INSTANCE), headAtom.getArgument(0), headAtom.getArgument(1)); 
		if (p instanceof Inequality) 
			return Atom.create(getTrackingDLPredicate((Inequality) p), headAtom.getArgument(0), headAtom.getArgument(1)); 

		return null;
	}

	private Atom getGapAtom(Atom headAtom) {
		DLPredicate p = headAtom.getDLPredicate(); 
		if (p instanceof AtLeastConcept) {
			return Atom.create(getGapDLPredicate(AtomicConcept.create(Normalisation.getAuxiliaryConcept4Disjunct((AtLeastConcept) p))), headAtom.getArgument(0)); 
		}
		if (p instanceof AtomicConcept) 
			return Atom.create(getGapDLPredicate((AtomicConcept) p), headAtom.getArgument(0)); 
		if (p instanceof AtomicRole) 
			return Atom.create(getGapDLPredicate((AtomicRole) p), headAtom.getArgument(0), headAtom.getArgument(1));
		if (p instanceof Equality || p instanceof AnnotatedEquality) 
			return Atom.create(getGapDLPredicate(Equality.INSTANCE), headAtom.getArgument(0), headAtom.getArgument(1)); 
		if (p instanceof Inequality) 
			return Atom.create(getGapDLPredicate((Inequality) p), headAtom.getArgument(0), headAtom.getArgument(1)); 

		return null;
	}

	private void encodingDisjunctiveRule(DLClause clause) {
		int headLength = clause.getHeadLength();
		
		Atom[] auxAtoms = new Atom[headLength];
		for (int i = 0; i < headLength; ++i)
			auxAtoms[i] = getAuxiliaryAtom(clause.getHeadAtom(i));
		
		Atom[] trackingAtoms = new Atom[headLength];
		for (int i = 0; i < headLength; ++i)
			trackingAtoms[i] = getTrackingAtom(clause.getHeadAtom(i));
		
		Atom[] gapAtoms = new Atom[headLength];
		for (int i = 0; i < headLength; ++i)
			gapAtoms[i] = getGapAtom(clause.getHeadAtom(i));
		
		Atom[] bodyAtoms = clause.getBodyAtoms();
		
		LinkedList<Atom> newHeadAtoms = new LinkedList<Atom>();
		DLPredicate selected = AtomicConcept.create(getSelectedPredicate()); 
		newHeadAtoms.add(Atom.create(selected, getIndividual4GeneralRule(clause)));
		
		for (Atom atom: bodyAtoms) {
			Atom newAtom = Atom.create(
					getTrackingDLPredicate(atom.getDLPredicate()), 
					DLClauseHelper.getArguments(atom));
			newHeadAtoms.add(newAtom);
		}

		DLClause newClause;
		for (int j = 0; j < headLength; ++j) {
			Atom[] newBodyAtoms = new Atom[headLength + bodyAtoms.length + 1];
			newBodyAtoms[0] = gapAtoms[j];
			for (int i = 0; i < headLength; ++i)
				if (i != j)
//					newBodyAtoms[i] = auxAtoms[i];
					newBodyAtoms[i + 1] = auxAtoms[i];
				else 
//					newBodyAtoms[j] = trackingAtoms[j]; 
					newBodyAtoms[j + 1] = trackingAtoms[j]; 
			
			for (int i = 0; i < bodyAtoms.length; ++i)
//				newBodyAtoms[i + headLength] = bodyAtoms[i]; 
				newBodyAtoms[i + headLength + 1] = bodyAtoms[i]; 
			
			for (Atom atom: newHeadAtoms) {
				newClause = DLClause.create(new Atom[] {atom}, newBodyAtoms); 
				addTrackingClause(newClause);
			}
		}
	}
	
	protected void addTrackingClause(DLClause clause) {
		trackingClauses.add(clause); 
	}

	protected void addDisjunctiveRule(DLClause clause) {
		disjunctiveRules.add(clause);
	}
	
	protected DLPredicate getAuxPredicate(DLPredicate p) {
		if (p instanceof AtLeastConcept) {
			StringBuilder builder = new StringBuilder(
					Normalisation.getAuxiliaryConcept4Disjunct((AtLeastConcept) p));
			builder.append("_AUXa").append(currentQuery.getQueryID()); 
			return AtomicConcept.create(builder.toString()); 
		}
		
		return getDLPredicate(p, "_AUXa" + currentQuery.getQueryID());
	}

	protected DLPredicate getTrackingBottomDLPredicate(DLPredicate p) {
		return getDLPredicate(p, getTrackingSuffix("0"));
	}

	private DLPredicate generateAuxiliaryRule(AtLeastConcept p, boolean withAux) {
		int num = p.getNumber(); 
		Variable[] Ys = new Variable[num]; 
		if (num > 1)
			for (int i = 0; i < num; ++i) 
				Ys[i] = Variable.create("Y" + (i + 1));
		else 
			Ys[0] = Y; 
		
		Collection<Atom> expandedAtom = new LinkedList<Atom>(); 
		Collection<Atom> representativeAtom = new LinkedList<Atom>(); 
		if (p.getOnRole() instanceof AtomicRole) {
			AtomicRole r = (AtomicRole) p.getOnRole(); 
			for (int i = 0; i < num; ++i) 
				expandedAtom.add(Atom.create(r, X, Ys[i]));
			representativeAtom.add(Atom.create(r, X, Ys[0])); 
		}
		else {
			AtomicRole r = ((InverseRole) p.getOnRole()).getInverseOf(); 
			for (int i = 0; i < num; ++i) 
				expandedAtom.add(Atom.create(r, Ys[i], X));
			representativeAtom.add(Atom.create(r, Ys[0], X)); 
		}
		
		if (num > 1) {
			representativeAtom.add(Atom.create(Inequality.INSTANCE, Ys[0], Ys[1])); 
		}
		for (int i = 0; i < num; ++i)
			for (int j = i + 1; j < num; ++j)
				expandedAtom.add(Atom.create(Inequality.INSTANCE, Ys[i], Ys[j])); 
		
		if (!p.getToConcept().equals(AtomicConcept.THING)) {
			AtomicConcept c; 
			if (p.getToConcept() instanceof AtomicConcept) 
				c = (AtomicConcept) p.getToConcept();
			else {
				c = OverApproxExist.getNegationConcept(((AtomicNegationConcept) p.getToConcept()).getNegatedAtomicConcept());
			}
			for (int i = 0; i < num; ++i)
				expandedAtom.add(Atom.create(c, Ys[i])); 
			representativeAtom.add(Atom.create(c, Ys[0]));
		}

		AtomicConcept ac = AtomicConcept.create(Normalisation.getAuxiliaryConcept4Disjunct(p));
		DLPredicate trackingPredicate = getTrackingDLPredicate(ac); 
		DLPredicate gapPredicate = getGapDLPredicate(ac); 
		DLPredicate auxPredicate = withAux ? getAuxPredicate(p) : null;
		
		for (Atom atom: representativeAtom) {
			Atom[] bodyAtoms = new Atom[expandedAtom.size() + 1]; 
			if (atom.getArity() == 1)
				bodyAtoms[0] = Atom.create(getTrackingDLPredicate(atom.getDLPredicate()), atom.getArgument(0));
			else 
				bodyAtoms[0] = Atom.create(getTrackingDLPredicate(atom.getDLPredicate()), atom.getArgument(0), atom.getArgument(1));
			int i = 0; 
			for (Atom bodyAtom: expandedAtom)
				bodyAtoms[++i] = bodyAtom;  
			addTrackingClause(DLClause.create(new Atom[] {Atom.create(trackingPredicate, X)}, bodyAtoms));
			
			bodyAtoms = new Atom[expandedAtom.size() + 1]; 
			if (atom.getArity() == 1)
				bodyAtoms[0] = Atom.create(getGapDLPredicate(atom.getDLPredicate()), atom.getArgument(0));
			else 
				bodyAtoms[0] = Atom.create(getGapDLPredicate(atom.getDLPredicate()), atom.getArgument(0), atom.getArgument(1));
			i = 0; 
			for (Atom bodyAtom: expandedAtom)
				bodyAtoms[++i] = bodyAtom;  
			addTrackingClause(DLClause.create(new Atom[] {Atom.create(gapPredicate, X)}, bodyAtoms));
			
			if (withAux) {
				bodyAtoms = new Atom[expandedAtom.size() + 1]; 
				bodyAtoms[0] = getAuxiliaryAtom(atom);
				i = 0; 
				for (Atom bodyAtom: expandedAtom)
					bodyAtoms[++i] = bodyAtom;  
				addTrackingClause(DLClause.create(new Atom[] {Atom.create(auxPredicate, X)}, bodyAtoms));
			}
		}
		
		return withAux ? auxPredicate : trackingPredicate;
	}

	protected DLPredicate generateAuxiliaryRule(AtomicRole p) {
		if (currentQuery.isBottom()) 
			return getTrackingDLPredicate(p);
		
		DLPredicate ret = getAuxPredicate(p); 
		Atom[] headAtom = new Atom[] {Atom.create(ret, X, Y)};

		addTrackingClause(
				DLClause.create(headAtom, new Atom[] {Atom.create(getTrackingDLPredicate(p), X, Y)})); 
		addTrackingClause(
				DLClause.create(headAtom, new Atom[] {Atom.create(getTrackingBottomDLPredicate(p), X, Y)})); 
		
		return ret; 
	}
	
	protected Variable X = Variable.create("X");
	protected Variable Y = Variable.create("Y"); 

	protected DLPredicate generateAuxiliaryRule(AtomicConcept p) {
		if (currentQuery.isBottom())
			return getTrackingDLPredicate(p); 
		
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

	private DLPredicate generateAuxiliaryRule(Equality instance) {
		return generateAuxiliaryRule(AtomicRole.create(Namespace.EQUALITY));
	}

	private DLPredicate generateAuxiliaryRule(Inequality instance) {
		return generateAuxiliaryRule(AtomicRole.create(Namespace.INEQUALITY)); 
	}
	
	@Override
	public String getTrackingProgram() {
		StringBuilder sb = getTrackingProgramBody();
		if (currentQuery.isBottom())
			sb.append(getBottomTrackingProgram()); 
		sb.insert(0, MyPrefixes.PAGOdAPrefixes.prefixesText()); 
		
//		///////
// 		System.out.println("printing from TrackingRuleEncoderDisjVar1");
//		System.out.println(sb.toString());
//		///////
		
		return sb.toString(); 
	}

	private String bottomTrackingProgram = null; 

	private String getBottomTrackingProgram() {
		if (bottomTrackingProgram != null) return bottomTrackingProgram.replace("_tn", getTrackingPredicate(""));  
		
		String bottomSuffix = getTrackingSuffix("0"); 
		LinkedList<DLClause> clauses = new LinkedList<DLClause>();  
		Variable X = Variable.create("X"); 
		for (String concept: unaryPredicates)
			clauses.add(DLClause.create(new Atom[] {Atom.create(AtomicConcept.create(concept + bottomSuffix) , X)}, 
										new Atom[] {Atom.create(AtomicConcept.create(concept + "_tn"), X)}));
		Variable Y = Variable.create("Y"); 
		for (String role: binaryPredicates)
			clauses.add(DLClause.create(new Atom[] {Atom.create(AtomicRole.create(role + bottomSuffix) , X, Y)}, 
										new Atom[] {Atom.create(AtomicRole.create(role + "_tn"), X, Y) }));
		
		StringBuilder builder = new StringBuilder(DLClauseHelper.toString(clauses));
		bottomTrackingProgram = builder.toString();
		return bottomTrackingProgram.replace("_tn", getTrackingPredicate("")); 
	}

	private void encodingBottomQueryClause(DLClause clause) {
		Term t; 
		for (Atom tAtom: clause.getHeadAtoms()) {
			for (int i = 0; i < tAtom.getArity(); ++i)
				if ((t = tAtom.getArgument(i)) instanceof Individual) 
					if (((Individual) t).getIRI().startsWith(OverApproxExist.skolemisedIndividualPrefix))
						clause = program.getCorrespondingClause(clause); 				
		}
		
		LinkedList<Atom> newHeadAtoms = new LinkedList<Atom>();
		newHeadAtoms.add(Atom.create(selected, getIndividual4GeneralRule(clause)));
		
		for (Atom atom: clause.getBodyAtoms()) {
			atom = Atom.create(
					getTrackingDLPredicate(atom.getDLPredicate()), 
					DLClauseHelper.getArguments(atom));
			newHeadAtoms.add(atom);
		}

		DLClause newClause;
		
		int offset = (clause.getBodyLength() == 1 && clause.getBodyAtom(0).getDLPredicate().toString().contains("owl:Nothing")) ? 1 : 2; 
		
		DLPredicate trackingPredicate, p; 
		for (Atom headAtom: clause.getHeadAtoms()) {
			Atom[] newBodyAtoms = new Atom[clause.getBodyLength() + offset];
			if ((p = headAtom.getDLPredicate()) instanceof AtLeastConcept) {
				trackingPredicate = generateAuxiliaryRule((AtLeastConcept) p, false);
				p = AtomicConcept.create(Normalisation.getAuxiliaryConcept4Disjunct((AtLeastConcept) p));
			}
			else 
				trackingPredicate = getTrackingDLPredicate(p); 
			newBodyAtoms[0] = Atom.create(
					trackingPredicate, 
					DLClauseHelper.getArguments(headAtom));
			
			if (offset == 2)
			newBodyAtoms[1] = Atom.create(
					getGapDLPredicate(p), 
					DLClauseHelper.getArguments(headAtom));
	
			for (int i = 0; i < clause.getBodyLength(); ++i)
				newBodyAtoms[i + offset] = clause.getBodyAtom(i); 
			
			for (Atom atom: newHeadAtoms) {
				newClause = DLClause.create(new Atom[] {atom}, newBodyAtoms); 
				trackingClauses.add(newClause);
			}
		}
	}
	
}
