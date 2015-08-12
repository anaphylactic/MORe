package org.semanticweb.more.pagoda.rules;
import java.util.Collection;
import java.util.LinkedList;

import org.semanticweb.HermiT.model.AtLeast;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;

import uk.ac.ox.cs.pagoda.rules.Approximator;



public class IgnoreBothAndHasValue implements Approximator {

//	@Override
//	public Collection<DLClause> convert(DLClause clause, DLClause originalClause) {
//		Collection<DLClause> ret = new LinkedList<DLClause>();
//		
//		if (clause.getHeadLength() > 1) return ret;
//		
//		if (clause.getHeadLength() > 0) {
//			DLPredicate predicate = clause.getHeadAtom(0).getDLPredicate();
//			
//			if (predicate instanceof AtLeast) return ret; 
//		}
//		
//		ret.add(clause); 
//		return ret; 
//	}
	
	@Override
	public Collection<DLClause> convert(DLClause clause, DLClause originalClause) {
		Collection<DLClause> ret = new LinkedList<DLClause>();
		
		if (clause.getHeadLength() > 1) 
			return ret;
		
		if (clause.getHeadLength() > 0) {
			DLPredicate predicate = clause.getHeadAtom(0).getDLPredicate();
			
			if (predicate instanceof AtLeast || predicate.getArity() > 1 ) 
				return ret; 
		}
		
		ret.add(clause); 
		return ret; 
	}
}
