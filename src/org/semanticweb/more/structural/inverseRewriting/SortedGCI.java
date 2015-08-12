package org.semanticweb.more.structural.inverseRewriting;

import java.util.ArrayList;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;

public class SortedGCI{
	public ArrayList<OWLClass> lhsAtomic = new ArrayList<OWLClass>();
	public ArrayList<OWLObjectSomeValuesFrom> lhsExistential = new ArrayList<OWLObjectSomeValuesFrom>();
	public ArrayList<OWLClass> rhsAtomic = new ArrayList<OWLClass>();
	public ArrayList<OWLClassExpression> rhsExistential = new ArrayList<OWLClassExpression>();
	public ArrayList<OWLObjectAllValuesFrom> rhsUniversal = new ArrayList<OWLObjectAllValuesFrom>();
	public ArrayList<OWLObjectMaxCardinality> rhsMaxCard = new ArrayList<OWLObjectMaxCardinality>();
	public ArrayList<OWLObjectOneOf> rhsOneof = new ArrayList<OWLObjectOneOf>();
	
	
	public void clear(){
		lhsAtomic.clear();
		lhsExistential.clear();
		rhsAtomic.clear();
		rhsExistential.clear();
		rhsUniversal.clear();
		rhsMaxCard.clear();
		rhsOneof.clear();
	}
	
	public void addLhsAtomic(OWLClass c){
		lhsAtomic.add(c);
	}
	public void addLhsExist(OWLObjectSomeValuesFrom some){
		lhsExistential.add(some);
	}
	public void addRhsAtomic(OWLClass c){
		rhsAtomic.add(c);
	}
	public void addRhsExist(OWLClassExpression some){
		rhsExistential.add(some);
	}
	public void addRhsUniv(OWLObjectAllValuesFrom all){
		rhsUniversal.add(all);
	}
	public void addRhsMaxCard(OWLObjectMaxCardinality max){
		rhsMaxCard.add(max);
	}
	public void addRhsOneOf(OWLObjectOneOf one){
		rhsOneof.add(one);
	}
	
	public String toString(){
		String s = "";
		boolean first = true;
		for (OWLClassExpression c : lhsExistential){
			if (!first)
				s = s + " AND ";
			s = s + c.toString();
			first = false;
		}
		for (OWLClassExpression c : lhsAtomic){
			if (!first)
				s = s + " AND ";
			s = s + c.toString();
			first = false;
		}
		if (first)
			s = s + "TOP";
		
		s = s + " --> ";
		
		
		first = true;
		for (OWLClassExpression c : rhsUniversal){
			if (!first)
				s = s + " OR ";
			s = s + c.toString();
			first = false;
		}
		for (OWLClassExpression c : rhsMaxCard){
			if (!first)
				s = s + " OR ";
			s = s + c.toString();
			first = false;
		}
		for (OWLClassExpression c : rhsExistential){
			if (!first)
				s = s + " OR ";
			s = s + c.toString();
			first = false;
		}
		for (OWLClassExpression c : rhsAtomic){
			if (!first)
				s = s + " OR ";
			s = s + c.toString();
			first = false;
		}
		for (OWLClassExpression c : rhsOneof){
			if (!first)
				s = s + " OR ";
			s = s + c.toString();
			first = false;
		}
		if (first)
			s = s + " BOT ";
		return s;
	}
}
