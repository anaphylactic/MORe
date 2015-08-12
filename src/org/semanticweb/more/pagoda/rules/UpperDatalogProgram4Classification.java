package org.semanticweb.more.pagoda.rules;


import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLOntology;

import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.rules.UpperDatalogProgram;


public class UpperDatalogProgram4Classification extends UpperDatalogProgram {

	Collection<DLClause> auxiliaryClauses = new HashSet<DLClause>();
	@Override
	protected void initApproximator() {
		m_approx = new OverApproxBoth4Classification(); 
	}

	public Set<Atom> getAdditionalFacts(){
		return ((OverApproxBoth4Classification) m_approx).getAdditionalFacts();
	}
	
	@Override
	public void transform() {
		super.transform();
//		clauses.addAll(((OverApproxBoth4Classification) m_approx).getAuxiliaryClauses());
		auxiliaryClauses.addAll(((OverApproxBoth4Classification) m_approx).getAuxiliaryClauses());
	}

	public Collection<DLClause> getAuxiliaryClauses() {
		return auxiliaryClauses;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder(toString(clauses));
		sb.append(DLClauseHelper.toString(auxiliaryClauses));
		return sb.toString(); 
	}
	
	public DLOntology getDLOntology(){
		return dlOntology;
	}
}
