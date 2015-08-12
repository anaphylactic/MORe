package org.semanticweb.more.visitors;

import java.util.Iterator;

import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDatatypeDefinitionAxiom;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLHasKeyAxiom;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.SWRLRule;


public class HornSHIFAxiomVisitor implements OWLFragmentVisitor {

	private boolean isHornSHIF;
	

	public boolean isHornSHIF() {
		return isHornSHIF;
	}

	public boolean isInFragment() {
		return isHornSHIF;
	}
		
	/*
	 * axioms in HornSHIF
	 */
	
	@Override
	public void visit(OWLSubClassOfAxiom axiom){
		SHIFClassExpressionVisitor classExpVisitor = new SHIFClassExpressionVisitor();
		OWLClassExpression subClass = axiom.getSubClass();
		OWLClassExpression superClass = axiom.getSuperClass();
		isHornSHIF = classExpVisitor.isSHIF(subClass) && classExpVisitor.isSHIF(superClass);		
		if (isHornSHIF){
			isHornSHIF = containsNoPositiveDisjunction(superClass) && containsNoNegativeDisjunction(subClass) &&
					//containsNoPositiveMaxCardGt1(superClass) && containsNoNegativeMaxCardGt1(subClass) &&
					containsNoPositiveNegation(subClass) && containsNoNegativeNegation(superClass) &&
					containsNoPositiveAllValues(subClass) && containsNoNegativeAllValues(superClass) &&
					containsNoPositiveMinCard(subClass) && containsNoNegativeMinCard(superClass);
			//&& containsNoPositiveMaxCard(subClass) && containsNoNegativeMaxCard(superClass);
		}
	}
	
	@Override
	public void visit(OWLEquivalentClassesAxiom axiom){
		SHIFClassExpressionVisitor classExpVisitor = new SHIFClassExpressionVisitor();
		Iterator<OWLClassExpression> iterator = axiom.getClassExpressions().iterator();
		isHornSHIF = true;
		while (isHornSHIF && iterator.hasNext()){
			OWLClassExpression exp = iterator.next();
			isHornSHIF = (classExpVisitor.isSHIF(exp)) && 
					containsNoPositiveDisjunction(exp) && containsNoNegativeDisjunction(exp) &&
					//containsNoPositiveMaxCardGt1(exp) && containsNoNegativeMaxCardGt1(exp) &&
					containsNoPositiveNegation(exp) && containsNoNegativeNegation(exp) &&
					containsNoPositiveAllValues(exp) && containsNoNegativeAllValues(exp) &&
					containsNoPositiveMinCard(exp) && containsNoNegativeMinCard(exp);
			//&& containsNoPositiveMaxCard(exp) && containsNoNegativeMaxCard(exp);
		}
	}
	
	@Override
	public void visit(OWLDisjointClassesAxiom axiom) {
		//this can be rewritten into axioms of the form   A & B -> BOT 
		//so what we need is for all classExpressions to be suitable for the lhs of a subClassOf axiom
//		isHornSHIF = false;
		SHIFClassExpressionVisitor classExpVisitor = new SHIFClassExpressionVisitor();
		Iterator<OWLClassExpression> iterator = axiom.getClassExpressions().iterator();
		isHornSHIF = true;
		while (isHornSHIF && iterator.hasNext()){
			OWLClassExpression exp = iterator.next();
			isHornSHIF = (classExpVisitor.isSHIF(exp)) && 
					containsNoNegativeDisjunction(exp) &&
					//containsNoNegativeMaxCardGt1(exp) &&
					containsNoPositiveNegation(exp) &&
					containsNoPositiveAllValues(exp) &&
					containsNoPositiveMinCard(exp);
			// && containsNoPositiveMaxCard(exp);
		}
	}
	
	@Override
	public void visit(OWLSubObjectPropertyOfAxiom axiom) {
		isHornSHIF = true;
	}
	
	@Override
	public void visit(OWLSubPropertyChainOfAxiom axiom) {
		isHornSHIF = false;
	}
	
	@Override
	public void visit(OWLSubDataPropertyOfAxiom axiom) {
		isHornSHIF = false;//CB does not accept this
	}
	
	@Override
	public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
		isHornSHIF = true;
	}
	
	@Override
	public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
		isHornSHIF = false;//CB does not accept this
	}
	
	@Override
	public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
		isHornSHIF = true;
	}
	
	@Override
	public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
		isHornSHIF = false;
	}
		
	@Override
	public void visit(OWLObjectPropertyDomainAxiom axiom) {
		//this can be rewritten into   exists R. TOP -> A 
		//so what we need is for the domain classExpression to be suitable for the rhs of a subClassOf axiom
//		isHornSHIF = false;
		SHIFClassExpressionVisitor classExpVisitor = new SHIFClassExpressionVisitor();
		OWLClassExpression domain = axiom.getDomain();
		isHornSHIF = classExpVisitor.isSHIF(domain) && 
				containsNoPositiveDisjunction(domain) &&
				//containsNoPositiveMaxCardGt1(domain) &&
				containsNoNegativeNegation(domain) &&
				containsNoNegativeAllValues(domain) &&
				containsNoNegativeMinCard(domain);
		// && containsNoNegativeMaxCard(domain);
	}

	@Override
	public void visit(OWLDataPropertyDomainAxiom axiom) {
		//this can be rewritten into   exists R. dataTOP -> A 
		//so what we need is for the domain classExpression to be suitable for the rhs of a subClassOf axiom
		SHIFClassExpressionVisitor classExpVisitor = new SHIFClassExpressionVisitor();
		OWLClassExpression domain = axiom.getDomain();
		isHornSHIF = classExpVisitor.isSHIF(domain) && 
				containsNoPositiveDisjunction(domain) &&
				//containsNoPositiveMaxCardGt1(domain) &&
				containsNoNegativeNegation(domain) &&
				containsNoNegativeAllValues(domain) &&
				containsNoNegativeMinCard(domain);
		// && containsNoNegativeMaxCard(domain);
	}
	
	@Override
	public void visit(OWLObjectPropertyRangeAxiom axiom) {
		//this can be rewritten into   exists inv(R). TOP -> A 
		//so what we need is for the domain classExpression to be suitable for the rhs of a subClassOf axiom
//		isHornSHIF = false;
		SHIFClassExpressionVisitor classExpVisitor = new SHIFClassExpressionVisitor();
		OWLClassExpression range = axiom.getRange();
		isHornSHIF = classExpVisitor.isSHIF(range) && 
				containsNoPositiveDisjunction(range) &&
				//containsNoPositiveMaxCardGt1(range) &&
				containsNoNegativeNegation(range) &&
				containsNoNegativeAllValues(range) &&
				containsNoNegativeMinCard(range) ;
		//&& containsNoNegativeMaxCard(range);
	}
	
	@Override
	public void visit(OWLDataPropertyRangeAxiom axiom) {
		isHornSHIF = false;//????? CB does not accept this
	}
	
	@Override
	public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
		isHornSHIF = true;
	}
	
	@Override
	public void visit(OWLFunctionalDataPropertyAxiom axiom) {
		isHornSHIF = false;//????? CB does not accept this
	}
	
	@Override
	public void visit(OWLHasKeyAxiom axiom) {
		isHornSHIF = true;//????????????????????????
	}
	
	@Override
	public void visit(OWLDeclarationAxiom axiom) {
		isHornSHIF = true;
	}	
	
	@Override
	public void visit(OWLInverseObjectPropertiesAxiom axiom) {
		isHornSHIF = true;
	}
	/*
	 * END AXIOMS SUPPORTED BY CB REASONER
	 */

	
	/*
	 * TERMINOLOGICAL AXIOMS NOT SUPPORTED BY ELK REASONER
	 */
	@Override
	public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLDisjointDataPropertiesAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLDisjointUnionAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
		isHornSHIF = false;
	}
	
	@Override
	public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
		isHornSHIF = true;
	}

	@Override
	public void visit(OWLDatatypeDefinitionAxiom axiom) {		
		isHornSHIF = true;//????????
	}
	
	//should we ignore this??
	@Override
	public void visit(SWRLRule axiom) {
		isHornSHIF = true;
	}
	
	/*
	 * END: TERMINOLOGICAL AXIOMS NOT SUPPORTED BY ELK REASONER
	 */	
	
	
	/*
	 * ASSERTION/ANNOTATION AXIOMS (IGNORED AXIOMS)
	 */
	
	@Override
	public void visit(OWLAnnotationAssertionAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLSubAnnotationPropertyOfAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLAnnotationPropertyDomainAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLAnnotationPropertyRangeAxiom axiom) {
		isHornSHIF = false;
	}
	
	@Override
	public void visit(OWLClassAssertionAxiom axiom) {
		isHornSHIF = false;
	}
	
	@Override
	public void visit(OWLObjectPropertyAssertionAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLDataPropertyAssertionAxiom axiom) {
		isHornSHIF = false;
	}
	
	@Override
	public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
		isHornSHIF = false;
	}
	
	@Override
	public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
		isHornSHIF = false;
	}

	@Override
	public void visit(OWLSameIndividualAxiom axiom) {
		isHornSHIF = false;
	}
	
	@Override
	public void visit(OWLDifferentIndividualsAxiom axiom) {
		isHornSHIF = false;
	}
	
	/*
	 * END: ASSERTION/ANNOTATION AXIOMS (IGNORED AXIOMS)
	 */
	
//	private boolean containsNoNegativeMaxCard(OWLClassExpression classExp) {
//		NegOccurrenceVisitor visitor = new NegOccurrenceVisitor("maxCard");
//		return !visitor.containsNegOccurrence(classExp);
//	}
//
//	private boolean containsNoPositiveMaxCard(OWLClassExpression classExp) {
//		PosOccurrenceVisitor visitor = new PosOccurrenceVisitor("maxCard");
//		return !visitor.containsPosOccurrence(classExp);
//	}
//
//	private boolean containsNoNegativeMaxCardGt1(OWLClassExpression classExp) {
//		NegOccurrenceVisitor visitor = new NegOccurrenceVisitor("maxCardGt1");
//		return !visitor.containsNegOccurrence(classExp);
//	}
//
//	private boolean containsNoPositiveMaxCardGt1(OWLClassExpression classExp) {
//		PosOccurrenceVisitor visitor = new PosOccurrenceVisitor("maxCardGt1");
//		return !visitor.containsPosOccurrence(classExp);
//	}
	
	private boolean containsNoNegativeMinCard(OWLClassExpression classExp) {
		NegOccurrenceVisitor visitor = new NegOccurrenceVisitor("minCard");
		return !visitor.containsNegOccurrence(classExp);
	}

	private boolean containsNoPositiveMinCard(OWLClassExpression classExp) {
		PosOccurrenceVisitor visitor = new PosOccurrenceVisitor("minCard");
		return !visitor.containsPosOccurrence(classExp);
	}

	private boolean containsNoNegativeAllValues(OWLClassExpression classExp) {
		NegOccurrenceVisitor visitor = new NegOccurrenceVisitor("allValues");
		return !visitor.containsNegOccurrence(classExp);
	}

	private boolean containsNoPositiveAllValues(OWLClassExpression classExp) {
		PosOccurrenceVisitor visitor = new PosOccurrenceVisitor("allValues");
		return !visitor.containsPosOccurrence(classExp);
	}

	private boolean containsNoNegativeNegation(OWLClassExpression classExp) {
		NegOccurrenceVisitor visitor = new NegOccurrenceVisitor("negation");
		return !visitor.containsNegOccurrence(classExp);
	}

	private boolean containsNoPositiveNegation(OWLClassExpression classExp) {
		PosOccurrenceVisitor visitor = new PosOccurrenceVisitor("negation");
		return !visitor.containsPosOccurrence(classExp);
	}

	private boolean containsNoNegativeDisjunction(OWLClassExpression classExp) {
		NegOccurrenceVisitor visitor = new NegOccurrenceVisitor("union");
		return !visitor.containsNegOccurrence(classExp);
	}

	private boolean containsNoPositiveDisjunction(OWLClassExpression classExp) {
		PosOccurrenceVisitor visitor = new PosOccurrenceVisitor("union");
		return !visitor.containsPosOccurrence(classExp);
	}
	
	
	
	//------------------------
	
	
	
	protected class PosOccurrenceVisitor implements OWLClassExpressionVisitor{
		
		String classExpressionKind;
		boolean contains;
		
		public PosOccurrenceVisitor(String kind){
			classExpressionKind = kind;
		}

		
		public boolean containsPosOccurrence(OWLClassExpression ce){
			ce.accept(this);
			return contains;
		}
		
		
		@Override
		public void visit(OWLClass ce) {
			contains = false;
		}

		@Override
		public void visit(OWLObjectIntersectionOf ce) {
			boolean aux = false;
			for (OWLClassExpression op: ce.getOperands())
				 aux = aux || containsPosOccurrence(op);
			contains = aux;
		}

		@Override
		public void visit(OWLObjectUnionOf ce) {
			if (classExpressionKind.equals("union"))
				contains = true;	
			else{
				boolean aux = false;
				for (OWLClassExpression op: ce.getOperands())
					aux = aux || containsPosOccurrence(op);	
				contains = aux;
			}
		}

		@Override
		public void visit(OWLObjectComplementOf ce) {
			if (classExpressionKind.equals("negation"))
				contains = true;
			else{
				NegOccurrenceVisitor visitor = new NegOccurrenceVisitor(classExpressionKind);
				contains = visitor.containsNegOccurrence(ce.getOperand());	
			}
		}

		@Override
		public void visit(OWLObjectSomeValuesFrom ce) {
			contains = containsPosOccurrence(ce.getFiller());
		}

		@Override
		public void visit(OWLObjectAllValuesFrom ce) {
			if (classExpressionKind.equals("allValues"))
				contains = true;
			else{
				contains = containsPosOccurrence(ce.getFiller());	
			}
		}

		@Override
		public void visit(OWLObjectHasValue ce) {
			contains = false;
		}

		@Override
		public void visit(OWLObjectMinCardinality ce) {
			if (classExpressionKind.equals("minCard"))
				contains = true;	
			else{
				contains = containsPosOccurrence(ce.getFiller());				
			}
		}

		@Override
		public void visit(OWLObjectExactCardinality ce) {
			if (classExpressionKind.equals("minCard"))
				contains = true;
			else{
				NegOccurrenceVisitor visitor = new NegOccurrenceVisitor(classExpressionKind);
				contains = containsPosOccurrence(ce.getFiller()) 
						|| visitor.containsNegOccurrence(ce.getFiller());
			}
//			if (classExpressionKind.equals("maxCard"))
//				contains = true;	
//			else{
//				if (classExpressionKind.equals("minCard") || classExpressionKind.equals("maxCardGt1"))
//					contains = (ce.getCardinality() > 1);
//				else{
//					NegOccurrenceVisitor visitor = new NegOccurrenceVisitor(classExpressionKind);
//					contains = containsPosOccurrence(ce.getFiller()) 
//						|| visitor.containsNegOccurrence(ce.getFiller());
//				}
//			}
		}

		@Override
		public void visit(OWLObjectMaxCardinality ce) {
			NegOccurrenceVisitor visitor = new NegOccurrenceVisitor(classExpressionKind);
			contains = visitor.containsNegOccurrence(ce.getFiller());

//			if (classExpressionKind.equals("maxCard"))
//				contains = true;	
//			else{
//				if (classExpressionKind.equals("maxCardGt1"))
//					contains = (ce.getCardinality() > 1);
//				else{
//					NegOccurrenceVisitor visitor = new NegOccurrenceVisitor(classExpressionKind);
//					contains = visitor.containsNegOccurrence(ce.getFiller());
//				}
//			}
		}			

		@Override
		public void visit(OWLObjectHasSelf ce) {
			contains = false;
		}
		@Override
		public void visit(OWLObjectOneOf ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataSomeValuesFrom ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataAllValuesFrom ce) {
			contains = false;//????
		}
		@Override
		public void visit(OWLDataHasValue ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataMinCardinality ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataExactCardinality ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataMaxCardinality ce) {
			contains = false;
		}
	}
	
	private class NegOccurrenceVisitor implements OWLClassExpressionVisitor{
		
		String classExpressionKind;
		boolean contains;
		
		public NegOccurrenceVisitor(String kind){
			classExpressionKind = kind;
		}

		
		public boolean containsNegOccurrence(OWLClassExpression ce){
			ce.accept(this);
			return contains;
		}
		
		@Override
		public void visit(OWLClass ce) {
			contains = false;
		}

		@Override
		public void visit(OWLObjectIntersectionOf ce) {
			boolean aux = false;
			for (OWLClassExpression op: ce.getOperands())
				 aux = aux || containsNegOccurrence(op);
			contains = aux;
		}

		@Override
		public void visit(OWLObjectUnionOf ce) {
			boolean aux = false;
			for (OWLClassExpression op: ce.getOperands())
				aux = aux || containsNegOccurrence(op);	
		}

		@Override
		public void visit(OWLObjectComplementOf ce) {
			PosOccurrenceVisitor visitor = new PosOccurrenceVisitor(classExpressionKind);
			contains = visitor.containsPosOccurrence(ce.getOperand());	
		}

		@Override
		public void visit(OWLObjectSomeValuesFrom ce) {
			contains = containsNegOccurrence(ce.getFiller());
		}

		@Override
		public void visit(OWLObjectAllValuesFrom ce) {
			contains = containsNegOccurrence(ce.getFiller());	
		}

		@Override
		public void visit(OWLObjectHasValue ce) {
			contains = false;
		}

		@Override
		public void visit(OWLObjectMinCardinality ce) {
			contains = containsNegOccurrence(ce.getFiller());				
		}

		@Override
		public void visit(OWLObjectExactCardinality ce) {
			PosOccurrenceVisitor visitor = new PosOccurrenceVisitor(classExpressionKind);
			contains = containsNegOccurrence(ce.getFiller()) 
					|| visitor.containsPosOccurrence(ce.getFiller());
		}

		@Override
		public void visit(OWLObjectMaxCardinality ce) {
			PosOccurrenceVisitor visitor = new PosOccurrenceVisitor(classExpressionKind);
			contains = visitor.containsPosOccurrence(ce.getFiller());
		}			

		@Override
		public void visit(OWLObjectHasSelf ce) {
			contains = false;
		}
		@Override
		public void visit(OWLObjectOneOf ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataSomeValuesFrom ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataAllValuesFrom ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataHasValue ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataMinCardinality ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataExactCardinality ce) {
			contains = false;
		}
		@Override
		public void visit(OWLDataMaxCardinality ce) {
			contains = false;
		}
	}
}