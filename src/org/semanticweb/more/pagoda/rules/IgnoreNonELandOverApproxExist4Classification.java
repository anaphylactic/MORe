package org.semanticweb.more.pagoda.rules;
import java.util.Collection;
import java.util.LinkedList;

import org.semanticweb.HermiT.model.AtLeastDataRange;
import org.semanticweb.HermiT.model.DLClause;

import uk.ac.ox.cs.pagoda.rules.Approximator;


public class IgnoreNonELandOverApproxExist4Classification extends
		OverApproxExist4Classification implements Approximator {

	@Override
	public Collection<DLClause> convert(DLClause clause, DLClause originalClause) {
		Collection<DLClause> ret;
		switch (clause.getHeadLength()) {
		case 1:
			if (clause.getHeadAtom(0).getDLPredicate() instanceof AtLeastDataRange)
				return new LinkedList<DLClause>();
			return overApprox(clause.getHeadAtom(0), clause.getBodyAtoms(), originalClause);
		case 0:
			ret = new LinkedList<DLClause>();
			ret.add(clause); 
			return ret; 
		default:
			return super.convert(clause, originalClause);
		}
	}
}
