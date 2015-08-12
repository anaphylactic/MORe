package org.semanticweb.more.pagoda.rules;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.semanticweb.HermiT.model.AtLeastConcept;
import org.semanticweb.HermiT.model.AtLeastDataRange;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicNegationConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.model.Inequality;
import org.semanticweb.HermiT.model.InverseRole;
import org.semanticweb.HermiT.model.LiteralConcept;
import org.semanticweb.HermiT.model.Role;
import org.semanticweb.HermiT.model.Variable;

import uk.ac.ox.cs.pagoda.rules.OverApproxExist;

public class OverApproxExist4Classification extends OverApproxExist {
	
	protected Map<Role, AtomicRole> directionRole = new HashMap<Role, AtomicRole>();
	Variable Y = Variable.create("Y");
	
	protected Set<Atom> additionalFacts = new HashSet<Atom>();
	protected Set<DLClause> auxiliaryClauses = new HashSet<DLClause>();
	
	public Set<Atom> getAdditionalFacts(){
		return additionalFacts;
	}
	
	protected AtomicRole getDirectionPredicate(Role r){
		AtomicRole ret = null;
		AtomicRole originalAtomic;
		if (r instanceof AtomicRole){
			originalAtomic = (AtomicRole) r;
			ret = directionRole.get(originalAtomic);
			if (ret == null){
				ret = AtomicRole.create((originalAtomic).getIRI().toString()+"_directed");
				directionRole.put((AtomicRole) r, ret);
				auxiliaryClauses.add(DLClause.create(new Atom[]{Atom.create(originalAtomic, X,Y)}, new Atom[]{Atom.create(ret, X,Y)}));
				auxiliaryClauses.add(DLClause.create(new Atom[]{Atom.create(AtomicConcept.NOTHING, X)}, new Atom[]{Atom.create(ret, X,Y), Atom.create(AtomicConcept.NOTHING, Y)}));
			}
		} else{//it must be an instance of InverseRole
			originalAtomic = ((InverseRole) r).getInverseOf();
			ret = directionRole.get(originalAtomic);
			if (ret == null){
				ret = AtomicRole.create((originalAtomic).getIRI().toString()+"_directed");
				directionRole.put((AtomicRole) r, ret);
				auxiliaryClauses.add(DLClause.create(new Atom[]{Atom.create(originalAtomic, Y,X)}, new Atom[]{Atom.create(ret, X,Y)}));
				auxiliaryClauses.add(DLClause.create(new Atom[]{Atom.create(AtomicConcept.NOTHING, X)}, new Atom[]{Atom.create(ret, X,Y), Atom.create(AtomicConcept.NOTHING, Y)}));
			}
		}
		return ret;
	}

//	@Override
//	public Collection<DLClause> convert(DLClause clause, DLClause originalClause) {
//		Collection<DLClause> ret;
//		switch (clause.getHeadLength()) {
//		case 1:
//			return overApprox(clause.getHeadAtom(0), clause.getBodyAtoms(), originalClause);
//		case 0:
//			ret = new LinkedList<DLClause>();
//			ret.add(clause); 
//			return ret; 
//		default:
//			ret = new LinkedList<DLClause>();
//			for (Iterator<DLClause> iter = new DisjunctiveHeads(clause, originalClause); iter.hasNext(); )
//				ret.add(iter.next());
//			return ret;
//		}
//	}

//	
	
	public Collection<DLClause> overApprox(Atom headAtom, Atom[] bodyAtoms, DLClause originalClause, int offset) {
		Collection<DLClause> ret = new LinkedList<DLClause>(); 
		DLPredicate predicate = headAtom.getDLPredicate();
		if (predicate instanceof AtLeastConcept) {
			AtLeastConcept atLeastConcept = (AtLeastConcept) predicate;
			LiteralConcept concept = atLeastConcept.getToConcept();
			Role role = atLeastConcept.getOnRole();
			AtomicConcept atomicConcept = null;
			
			if (concept instanceof AtomicNegationConcept) {
				Atom atom1 = Atom.create(atomicConcept = ((AtomicNegationConcept) concept).getNegatedAtomicConcept(), X);
				Atom atom2 = Atom.create(atomicConcept = getNegationConcept(atomicConcept), X);
				ret.add(DLClause.create(new Atom[0], new Atom[] {atom1, atom2})); 
			}
			else {
				atomicConcept = (AtomicConcept) concept;
				if (atomicConcept.equals(AtomicConcept.THING))
					atomicConcept = null;
			}

			int card = atLeastConcept.getNumber(); 
			Individual[] individuals = new Individual[card];
			for (int i = 0; i < card; ++i) individuals[i] = getNewIndividual(originalClause, offset + i);
			
			for (int i = 0; i < card; ++i) {
//				if (atomicConcept != null)//TODO do sth with the ABox manager here - add facts for this individual with atomicConcept and also with top
//					ret.add(DLClause.create(new Atom[] {Atom.create(atomicConcept, individuals[i])}, bodyAtoms));
				additionalFacts.add(Atom.create(AtomicConcept.THING, individuals[i]));
				if (atomicConcept != null)
					additionalFacts.add(Atom.create(atomicConcept, individuals[i]));

//				Atom atom = role instanceof AtomicRole ?
//						Atom.create((AtomicRole) role, X, individuals[i]) : 
//						Atom.create(((InverseRole) role).getInverseOf(), individuals[i], X);
				Atom atom = Atom.create(getDirectionPredicate(role), X, individuals[i]);
				ret.add(DLClause.create(new Atom[] {atom}, bodyAtoms)); 
			}
			
			for (int i = 0; i < card; ++i)
				for (int j = i + 1; j < card; ++j)
					// TODO to be checked ... different as 
					ret.add(DLClause.create(new Atom[] {Atom.create(Inequality.INSTANCE, individuals[i], individuals[j])}, bodyAtoms)); 
							//DLClauseHelper.contructor_differentAs(individuals[i], individuals[j]));  
										
		}
		else if (predicate instanceof AtLeastDataRange) {
			// TODO to be implemented ... 
		}
		else
			ret.add(DLClause.create(new Atom[] {headAtom}, bodyAtoms)); 
		
		return ret; 
	}

	public Collection<DLClause> getAuxiliaryClauses(){
		return auxiliaryClauses;
	}
}
