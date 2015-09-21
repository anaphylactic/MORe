package uk.ac.ox.cs.pagoda.rules;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.ox.cs.pagoda.owl.OWLHelper;

public abstract class ApproxProgram extends Program {
	
	/**
	 * mapping from over-approximated DLClauses to DLClauses from the original ontology
	 */
	Map<DLClause, Object> correspondence = new HashMap<DLClause, Object>();
	
	protected Approximator m_approx = null; 
	
	protected ApproxProgram() { initApproximator(); }
	
	protected abstract void initApproximator(); 

	@Override
	public void transform() {
		super.transform();
		Iterator<DLClause> iterClause = transitiveClauses.iterator();
		for (Iterator<OWLTransitiveObjectPropertyAxiom> iterAxiom = transitiveAxioms.iterator(); iterAxiom.hasNext(); ) 
			addCorrespondence(iterClause.next(), iterAxiom.next()); 

		iterClause = subPropChainClauses.iterator(); 
		for (Iterator<OWLSubPropertyChainOfAxiom> iterAxiom = subPropChainAxioms.iterator(); iterAxiom.hasNext(); )
			addCorrespondence(iterClause.next(), iterAxiom.next()); 
	}

	@Override
	public Collection<DLClause> convert2Clauses(DLClause clause) {
		Collection<DLClause> ret = botStrategy.process(m_approx.convert(clause, clause));
//		OWLAxiom correspondingAxiom = OWLHelper.getOWLAxiom(ontology, clause); 
		for (DLClause newClause: ret) {
			addCorrespondence(newClause, clause);
//			addCorrespondence(newClause, correspondingAxiom);
		}
		return ret; 
	}
	
	private void addCorrespondence(DLClause newClause, Object corresponding) {
		Object object; 
		if ((object = correspondence.get(newClause)) != null) {
			if (object.equals(corresponding))
				return ; 
			
			if (object instanceof DLClause) {
				DLClause c1 = (DLClause) object;
				if (c1.getHeadLength() == 1) return ; 
				DLClause c2 = (DLClause) corresponding; 
				if (c2.getHeadLength() == 1) {
					correspondence.put(newClause, c2); 
					return ; 
				}
				ClauseSet list = new ClauseSet(c1, c2);
				correspondence.put(newClause, list); 
			}
			else if (object instanceof ClauseSet){
				ClauseSet list = (ClauseSet) object; 
				list.add((DLClause) corresponding); 
			}
		}
		correspondence.put(newClause, corresponding);
	}

	public OWLAxiom getEquivalentAxiom(DLClause clause) {
		Object obj = correspondence.get(clause);
		if (obj instanceof OWLAxiom)
			return (OWLAxiom) obj; 
		else if (obj != null){
			OWLAxiom ax = OWLHelper.getOWLAxiom(ontology, (DLClause) obj);
			return rewriteAxiom(ax);
		}
		else{
			OWLAxiom ax = OWLHelper.getOWLAxiom(ontology, clause);
			return rewriteAxiom(ax);
		}
	}
	
	protected OWLAxiom rewriteAxiom(OWLAxiom ax){
		if (ax instanceof OWLSubClassOfAxiom){
			OWLClassExpression subClass = ((OWLSubClassOfAxiom) ax).getSubClass();
			OWLClassExpression superClass = ((OWLSubClassOfAxiom) ax).getSuperClass();
			if (subClass.isOWLThing() && superClass instanceof OWLObjectHasSelf){//reflexive property axiom
				OWLObjectProperty p = ((OWLObjectHasSelf) ((OWLSubClassOfAxiom) ax).getSuperClass()).getProperty().getNamedProperty();
				ax = new OWLDataFactoryImpl().getOWLReflexiveObjectPropertyAxiom(p);
			}
			else if (subClass instanceof OWLObjectSomeValuesFrom && ((OWLObjectSomeValuesFrom) subClass).getFiller().isOWLThing() ){
				OWLObjectPropertyExpression p = ((OWLObjectSomeValuesFrom) subClass).getProperty();
				if (superClass instanceof OWLObjectAllValuesFrom && ((OWLObjectAllValuesFrom) superClass).getProperty().equals(p) ){//range axiom
					OWLClassExpression range = ((OWLObjectAllValuesFrom) superClass).getFiller();
					ax = new OWLDataFactoryImpl().getOWLObjectPropertyRangeAxiom(p, range);
				}
				else//domain axiom
					ax = new OWLDataFactoryImpl().getOWLObjectPropertyDomainAxiom(p, superClass);
			}
			else if (superClass instanceof OWLObjectAllValuesFrom && subClass instanceof OWLObjectIntersectionOf){
				OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) superClass).getProperty().getSimplified();
				Set<OWLClassExpression> conjunctsToKeep = new HashSet<OWLClassExpression>();
				boolean removedSomeConjuncts = false;
				for (OWLClassExpression e : ((OWLObjectIntersectionOf) subClass).getOperands())
					if (e instanceof OWLObjectSomeValuesFrom && ((OWLObjectSomeValuesFrom) e).getFiller().isOWLThing() && ((OWLObjectSomeValuesFrom) e).getProperty().getSimplified().equals(p))
						removedSomeConjuncts = true;
					else
						conjunctsToKeep.add(e);
				if (removedSomeConjuncts){
					OWLDataFactoryImpl factory = new OWLDataFactoryImpl();
					if (conjunctsToKeep.size() > 1)
						ax = new OWLDataFactoryImpl().getOWLSubClassOfAxiom(factory.getOWLObjectIntersectionOf(conjunctsToKeep), superClass);
					else if (conjunctsToKeep.size() == 1)
						ax = new OWLDataFactoryImpl().getOWLSubClassOfAxiom(conjunctsToKeep.iterator().next(), superClass);
					else{ //rangeAxiom; this case shouldn't really happen
						OWLClassExpression range = ((OWLObjectAllValuesFrom) superClass).getFiller();
						ax = new OWLDataFactoryImpl().getOWLObjectPropertyRangeAxiom(p, range);
					}
				}
			}
		}
		return ax;
	}

	public DLClause getCorrespondingClause(DLClause clause) {
		Object obj = correspondence.get(clause);
		if (obj instanceof DLClause)
			return (DLClause) obj; 
		else 
			return clause; 
	}
}

class ClauseSet extends HashSet<DLClause> {

	public ClauseSet(DLClause first, DLClause second) {
		add(first);  
		add(second); 
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
}