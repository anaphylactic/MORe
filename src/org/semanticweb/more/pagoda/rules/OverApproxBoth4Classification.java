package org.semanticweb.more.pagoda.rules;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Set;

import org.semanticweb.HermiT.model.AtLeastDataRange;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.DLClause;

import uk.ac.ox.cs.pagoda.rules.Approximator;
import uk.ac.ox.cs.pagoda.rules.OverApproxBoth;

public class OverApproxBoth4Classification extends OverApproxBoth {

	Approximator approxExist = new OverApproxExist4Classification();
	
	@Override
	public Collection<DLClause> convert(DLClause clause, DLClause originalClause) {
		Collection<DLClause> ret = new LinkedList<DLClause>(); 
		for (DLClause tClause: approxDist.convert(clause, originalClause)) {
			if (tClause.getHeadLength() > 0 && tClause.getHeadAtom(0).getDLPredicate() instanceof AtLeastDataRange) 
				continue; 
			ret.addAll(approxExist.convert(tClause, originalClause)); 
		}
		return ret; 
	}

	
	public Set<Atom> getAdditionalFacts(){
		return ((OverApproxExist4Classification) approxExist).getAdditionalFacts();
	}
	
	
	public Collection<DLClause> getAuxiliaryClauses(){
		return ((OverApproxExist4Classification) approxExist).getAuxiliaryClauses();
	}
}
