package org.semanticweb.more.structural;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class ObjectPropertyManager{

	//	Set<OWLObjectPropertyExpression> allRoles = new HashSet<OWLObjectPropertyExpression>();


	//We will use this class to compute the transitive reflexive closure of the role hierarchy 
	//and to compute the domain and range of all roles once that hierarchy is taken onto account

	Map<OWLObjectPropertyExpression, Set<OWLClass>> domainMap = new HashMap<OWLObjectPropertyExpression, Set<OWLClass>>();
	Map<OWLObjectPropertyExpression, Set<OWLClass>> rangeMap = new HashMap<OWLObjectPropertyExpression, Set<OWLClass>>();
	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> roleHierarchy = new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();
	boolean transitiveClosureOfRoleHierarchyComputed = false;

	Set<OWLObjectPropertyExpression> generatingRoles = new HashSet<OWLObjectPropertyExpression>();
	Set<OWLObjectProperty> nonSimpleRoles = new HashSet<OWLObjectProperty>();
	Set<OWLTransitiveObjectPropertyAxiom> transitivityAxioms = new HashSet<OWLTransitiveObjectPropertyAxiom>();


	Map<OWLObjectPropertyExpression, Map<OWLClass, OWLClass>> classesToEncodeTransitivityStandard = new HashMap<OWLObjectPropertyExpression, Map<OWLClass,OWLClass>>();
	Map<OWLObjectPropertyExpression, Map<OWLClass, OWLClass>> classesToEncodeTransitivityDisjointness = new HashMap<OWLObjectPropertyExpression, Map<OWLClass,OWLClass>>();//for cases  {some R. A  and  B   ->   bot}
	Map<OWLObjectPropertyExpression, Map<OWLClass, OWLClass>> classesDefUniv = new HashMap<OWLObjectPropertyExpression, Map<OWLClass,OWLClass>>();
	Map<OWLObjectPropertyExpression, Map<OWLClass, OWLClass>> classesDefExist = new HashMap<OWLObjectPropertyExpression, Map<OWLClass,OWLClass>>();
	static int freshClassCounter = 0;
	//find a way to register  generating roles and then add domain axioms for those roles which are generating

	Set<OWLSymmetricObjectPropertyAxiom> symmetricRoleAxioms = new HashSet<OWLSymmetricObjectPropertyAxiom>();
	boolean canIgnoreSymmetricRoleAxioms = false;
	Set<OWLAxiom> otherRoleAxioms = new HashSet<OWLAxiom>();

	OWLDataFactoryImpl factory = new OWLDataFactoryImpl();


	public void registerPropertyInclusion(OWLObjectPropertyExpression subP, OWLObjectPropertyExpression superP){
		subP = subP.getSimplified();
		superP = superP.getSimplified();

		Set<OWLObjectPropertyExpression> superProperties = roleHierarchy.get(subP); 
		if (superProperties != null){//then it must also contain inv(subP) as a key because we add both at the same time
			superProperties.add(superP);
			roleHierarchy.get(subP.getInverseProperty().getSimplified()).add(superP.getInverseProperty().getSimplified());
		}
		else{
			superProperties = new HashSet<OWLObjectPropertyExpression>();
			superProperties.add(subP);//necessary??
			superProperties.add(superP);
			roleHierarchy.put(subP, superProperties);

			Set<OWLObjectPropertyExpression> superPropertiesInv = new HashSet<OWLObjectPropertyExpression>();
			superPropertiesInv.add(subP.getInverseProperty().getSimplified());//necessary??
			superPropertiesInv.add(superP.getInverseProperty().getSimplified());
			roleHierarchy.put(subP.getInverseProperty().getSimplified(), superPropertiesInv);
		}
		otherRoleAxioms.add(factory.getOWLSubObjectPropertyOfAxiom(subP, superP));
	}

	public void registerComplexRoleInclusion(OWLSubPropertyChainOfAxiom ax){
		otherRoleAxioms.add(ax);
		nonSimpleRoles.add(ax.getSuperProperty().getNamedProperty());
	}

	public void registerRoleAxiom(OWLAxiom ax){
		otherRoleAxioms.add(ax);
	}
	public void registerSymmetricRoleAxiom(OWLSymmetricObjectPropertyAxiom ax){
		symmetricRoleAxioms.add(ax);
	}
	public Set<OWLSymmetricObjectPropertyAxiom> recoverIgnoredSymmetricRoleAxioms(){
		if (!canIgnoreSymmetricRoleAxioms)
			return new HashSet<OWLSymmetricObjectPropertyAxiom>();
		else
			return symmetricRoleAxioms;
	}

	public Set<OWLAxiom> getRoleAxioms(){
		return otherRoleAxioms;
	}

	public void registerDomain(OWLObjectPropertyExpression p, OWLClass domain){
		p = p.getSimplified();
		if (domainMap.containsKey(p))
			domainMap.get(p).add(domain);
		else{
			Set<OWLClass> aux = new HashSet<OWLClass>();
			aux.add(domain);
			domainMap.put(p, aux);
		}
		//		if (domainMap.containsKey(p))
		//			throw new IllegalArgumentException("more than one domain axiom for the same property!?!?");
		//		else
		//			domainMap.put(p, domain);
	}

	public void registerRange(OWLObjectPropertyExpression p, OWLClass range){
		//		OWLObjectPropertyExpression pInv = p.getInverseProperty().getSimplified();
		//		if (!domainMap.containsKey(pInv))
		//			domainMap.get(pInv).add(range);
		//		else{
		//			Set<OWLClass> aux = new HashSet<OWLClass>();
		//			aux.add(range);
		//			domainMap.put(pInv, aux);
		//		}
		p = p.getSimplified();
		if (rangeMap.containsKey(p))
			rangeMap.get(p).add(range);
		else{
			Set<OWLClass> aux = new HashSet<OWLClass>();
			aux.add(range);
			rangeMap.put(p, aux);
		}
		//		if (rangeMap.containsKey(p))
		//			throw new IllegalArgumentException("more than one range axiom for the same property!?!?");
		//		else
		//			domainMap.put(p, range);
	}

	//	public void registerTransitiveObjectProperty(OWLObjectPropertyExpression p){
	//		
	//	}

	public void registerTransitivityAxiom(OWLTransitiveObjectPropertyAxiom ax){
		transitivityAxioms.add(ax);
		nonSimpleRoles.add(ax.getProperty().getNamedProperty());
	}

	public Set<OWLTransitiveObjectPropertyAxiom> getTransitivityAxioms(){
		return transitivityAxioms;
	}

	protected OWLClassExpression getIntersection(OWLClassExpression c1, OWLClassExpression c2){
		Set<OWLClassExpression> operands = new HashSet<OWLClassExpression>();
		if (c1 instanceof OWLObjectIntersectionOf)
			operands.addAll(((OWLObjectIntersectionOf) c1).getOperands());
		else 
			operands.add(c1);
		if (c2 instanceof OWLObjectIntersectionOf)
			operands.addAll(((OWLObjectIntersectionOf) c2).getOperands());
		else 
			operands.add(c2);

		return factory.getOWLObjectIntersectionOf(operands);
	}


	public List<OWLClassExpression[]> handleRangesDomainsAndTransitivity(
			List<OWLClassExpression[]> conceptInclusions,
			boolean integrateRangesInRhsExistentials, boolean encodeTransitivity) {

		if (encodeTransitivity)
			return handleRangeDomainAndSymmetricRoleAxioms(encodeTransitivity(conceptInclusions), integrateRangesInRhsExistentials);
		else{
			otherRoleAxioms.addAll(transitivityAxioms);
			return handleRangeDomainAndSymmetricRoleAxioms(conceptInclusions, integrateRangesInRhsExistentials);
		}
		//		if (encodeTransitivity)
		//			return handleRangeAndDomainAxioms(encodeTransitivity(conceptInclusions), integrateRangesInRhsExistentials);
		//		else{
		//			otherRoleAxioms.addAll(transitivityAxioms);
		//			return handleRangeAndDomainAxioms(conceptInclusions, integrateRangesInRhsExistentials);
		//		}
	}

	public List<OWLClassExpression[]> encodeTransitivity(List<OWLClassExpression[]> inclusions){

		List<OWLClassExpression[]> updatedInclusions = new ArrayList<OWLClassExpression[]>();

		Set<OWLObjectPropertyExpression> transitiveRoles = new HashSet<OWLObjectPropertyExpression>();
		for (OWLTransitiveObjectPropertyAxiom ax : transitivityAxioms){
			OWLObjectPropertyExpression p = ax.getProperty();
			transitiveRoles.add(p.getSimplified());
			transitiveRoles.add(p.getInverseProperty().getSimplified());
		}
		if (!transitiveRoles.isEmpty()){
			//first of all we need to locate the roles that are superroles of some transitive object property
			//for that we first need to compute the transitive closure of the role hierarachy
			if (!transitiveClosureOfRoleHierarchyComputed)
				computeTransitiveClosureOfRoleHierarchy();
			Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> rolesWithTransitiveSubroles = new HashMap<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>();
			for (OWLObjectPropertyExpression p : transitiveRoles){
				Set<OWLObjectPropertyExpression> superroles = roleHierarchy.get(p);
				if (superroles != null)
					for (OWLObjectPropertyExpression q : superroles)
						if (rolesWithTransitiveSubroles.containsKey(q))
							rolesWithTransitiveSubroles.get(q).add(p);
						else{
							Set<OWLObjectPropertyExpression> aux = new HashSet<OWLObjectPropertyExpression>();
							aux.add(p);
							rolesWithTransitiveSubroles.put(q, aux);
						}
				if (rolesWithTransitiveSubroles.containsKey(p))
					rolesWithTransitiveSubroles.get(p).add(p);
				else{
					Set<OWLObjectPropertyExpression> aux = new HashSet<OWLObjectPropertyExpression>();
					aux.add(p);
					rolesWithTransitiveSubroles.put(p, aux);
				}
			}


			while (!inclusions.isEmpty()){

				OWLClassExpression[] inclusion = inclusions.remove(inclusions.size()-1); 

				//indexes for univ with atomic filler if we have to isolate them
				//indexes for univ with negative filler if we have to isolate them
				//#negative atoms other than univ with atomic filler - this inlcudes negated atoms, univ with negative filler and at most restrictions -- this will help decide if we have to isolate the universals or not
				//#atomic classes -- this will help decide if we have 

				Integer[] indexesForPositiveUniversalsWithTransitiveSubrole = new Integer[inclusion.length];
				int nPositiveUniversals = 0; //actually these are ONLY positive universals WITH transitive subrole
				Integer[] indexesForNegativeUniversalsWithTransitiveSubrole = new Integer[inclusion.length];
				int nNegativeUniversals = 0;
				int nOtherNegativeDisjuncts = 0;//anything that would put stuff on the body of a datalog rule other than a universal restriction with atomic filler and with a transitive subrole
				int nAtomicClasses = 0;
				int nNegatedAtomicClasses = 0;

				for (int i = 0 ; i<inclusion.length ; i++){
					if (inclusion[i] instanceof OWLObjectAllValuesFrom){
						OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) inclusion[i]).getProperty().getSimplified();
						if (rolesWithTransitiveSubroles.containsKey(p)){
							OWLClassExpression filler = ((OWLObjectAllValuesFrom) inclusion[i]).getFiller();
							if (filler instanceof OWLClass && !filler.isOWLNothing()){
								indexesForPositiveUniversalsWithTransitiveSubrole[nPositiveUniversals] = i;
								nPositiveUniversals++;
							}
							else if (((OWLObjectAllValuesFrom) inclusion[i]).getFiller().getComplementNNF() instanceof OWLClass || ((OWLObjectAllValuesFrom) inclusion[i]).getFiller().isOWLNothing()){
								indexesForNegativeUniversalsWithTransitiveSubrole[nNegativeUniversals] = i;
								nNegativeUniversals++;
								nOtherNegativeDisjuncts++;
							}
							else
								throw new IllegalStateException("filler in this universal restriction is not ok: " + inclusion[i].toString());
						}
						else nOtherNegativeDisjuncts++;
					}
					else if (inclusion[i] instanceof OWLClass){
						nAtomicClasses++;
					}
					else if (inclusion[i].getComplementNNF() instanceof OWLClass){
						nNegatedAtomicClasses++;
						nOtherNegativeDisjuncts++;
					}
					else if (inclusion[i] instanceof OWLObjectMaxCardinality	
							|| inclusion[i] instanceof OWLDataAllValuesFrom
							|| inclusion[i] instanceof OWLDataMaxCardinality){
						nOtherNegativeDisjuncts++;
					}
				}

				//				if (nPositiveUniversals > 0 && nNegativeUniversals > 0)
				//					System.out.println("HERE'S AN INTERESTING CASE!!");

				Object[] aux = treatRhsUniversalsForTransitivity(
						inclusion, 
						indexesForPositiveUniversalsWithTransitiveSubrole, 
						nPositiveUniversals, 
						nOtherNegativeDisjuncts,
						nNegatedAtomicClasses, 
						rolesWithTransitiveSubroles);
						
				updatedInclusions.addAll((Collection<OWLClassExpression[]>) aux[0]);
				int nNewAtomicClasses = (Integer) aux[1];
				nAtomicClasses = nAtomicClasses + nNewAtomicClasses;
				
//				int[] nNewAtomicClasses = new int[1];
//				updatedInclusions.addAll(treatRhsUniversalsForTransitivity(
//						inclusion, 
//						indexesForPositiveUniversalsWithTransitiveSubrole, 
//						nPositiveUniversals, 
//						nOtherNegativeDisjuncts,
//						nNegatedAtomicClasses, 
//						rolesWithTransitiveSubroles,
//						nNewAtomicClasses));
//				nAtomicClasses = nAtomicClasses + nNewAtomicClasses[0];


				updatedInclusions.addAll(treatLhsExistentialsForTransitivity(
						inclusion,
						indexesForNegativeUniversalsWithTransitiveSubrole,
						nNegativeUniversals,
						nAtomicClasses,
						nNegatedAtomicClasses,
						rolesWithTransitiveSubroles));

			}
		}
		else
			updatedInclusions = inclusions;

		return updatedInclusions;

	}

	protected Set<OWLClassExpression[]> treatLhsExistentialsForTransitivity(
			OWLClassExpression[] inclusion,
			Integer[] indexesForNegativeUniversalsWithTransitiveSubrole,
			int nNegativeUniversals,
			int nAtomicClasses,
			int nNegatedAtomicClasses,
			Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> rolesWithTransitiveSubroles) {

		Set<OWLClassExpression[]> finalInclusions = new HashSet<OWLClassExpression[]>();
		//		boolean anyLhsExistentialsTreated = false;

		//isolate universal restrictions with negated atomic fillers or not
		//the only cases where we don't isolate them is when we have {top -> all R. not A  or  B} or {top -> all R. not A  or  not B}
		//{top -> all R. not A  or  B}
		if (inclusion.length == 2 && nAtomicClasses == 1 && nNegativeUniversals == 1){
			//the original axiom stays
			finalInclusions.add(inclusion);

			OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) inclusion[indexesForNegativeUniversalsWithTransitiveSubrole[0]]).getProperty().getSimplified();
			OWLClassExpression filler = ((OWLObjectAllValuesFrom) inclusion[indexesForNegativeUniversalsWithTransitiveSubrole[0]]).getFiller();//must be negated atomic class or BOT

			if (!filler.isOWLNothing()){
				//o.w. it's jusr a domain axiom and we can just leave it as it is, no need to add anything extra
				OWLClass atomicClass = null;
				for (int i = 0 ; i<inclusion.length ; i++)
					if (inclusion[i] instanceof OWLClass)
						atomicClass = (OWLClass) inclusion[i];

				for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){

					//					anyLhsExistentialsTreated = true;

					OWLClassExpression[] copyOfInclusion = new OWLClassExpression[2];
					Object[] aux = getClassForTransitivity(t.getInverseProperty().getSimplified(), atomicClass);
					OWLClass c_invT_atomiClass = (OWLClass) aux[0];
					Boolean alreadyExists = (Boolean) aux[1];
					copyOfInclusion[0] = c_invT_atomiClass;
					copyOfInclusion[1] = factory.getOWLObjectAllValuesFrom(t, filler);
					finalInclusions.add(copyOfInclusion);

					if (!alreadyExists){
						finalInclusions.add(new OWLClassExpression[]{c_invT_atomiClass, factory.getOWLObjectAllValuesFrom(t, c_invT_atomiClass.getComplementNNF())});
						finalInclusions.add(new OWLClassExpression[]{c_invT_atomiClass.getComplementNNF(), atomicClass});
					}
				}
			}
		}
		//{top -> all R. not A  or  not B}
		else if (inclusion.length == 2 && nNegatedAtomicClasses == 1 && nNegativeUniversals == 1){
			// if the filler is BOT then maybe it's worth introducing an abbreviation for the negated atomic class 
			//and treating it as a domain axiom than adding all the extra aximos to encode transitivity

			//the original axiom stays
			finalInclusions.add(inclusion);

			OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) inclusion[indexesForNegativeUniversalsWithTransitiveSubrole[0]]).getProperty().getSimplified();
			OWLClassExpression filler = ((OWLObjectAllValuesFrom) inclusion[indexesForNegativeUniversalsWithTransitiveSubrole[0]]).getFiller();//must be negated atomic class
			OWLObjectComplementOf negatedAtomicClass = null;
			for (int i = 0 ; i<inclusion.length ; i++)
				if (inclusion[i].getComplementNNF() instanceof OWLClass)
					negatedAtomicClass = (OWLObjectComplementOf) inclusion[i];

			for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){

				//				anyLhsExistentialsTreated = true;

				Boolean alreadyExists = null;
				OWLClassExpression[] copyOfInclusion = new OWLClassExpression[2];
				Object[] aux = getClassForTransitivityDisjointness(t.getInverseProperty().getSimplified(), (OWLClass) negatedAtomicClass.getComplementNNF());
				OWLClass c_invT_atomiClass = (OWLClass) aux[0]; 
				alreadyExists = (Boolean) aux[1];
				copyOfInclusion[0] = c_invT_atomiClass;
				copyOfInclusion[1] = factory.getOWLObjectAllValuesFrom(t, filler);
				finalInclusions.add(copyOfInclusion);

				if (!alreadyExists){
					finalInclusions.add(new OWLClassExpression[]{c_invT_atomiClass, factory.getOWLObjectAllValuesFrom(t, c_invT_atomiClass.getComplementNNF())});
					finalInclusions.add(new OWLClassExpression[]{c_invT_atomiClass.getComplementNNF(), negatedAtomicClass});
				}
			}
		}
		else{

			//			////
			//			if (nNegativeUniversals > 0)
			//				System.out.println("look here!");
			//			////

			//probably also in this case if the filler of the universal restriction is BOT we can turn it into a "domain" axiom that doesn't need anything done to encode transitivity

			for (int j = 0 ; j<nNegativeUniversals ; j++){
				OWLClassExpression e = inclusion[indexesForNegativeUniversalsWithTransitiveSubrole[j]]; 
				if (e instanceof OWLObjectAllValuesFrom){
					OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) e).getProperty().getSimplified();
					OWLClassExpression filler = ((OWLObjectAllValuesFrom) e).getFiller();
					Object[] aux = null;
					if (filler.isOWLNothing())
						aux = getDefinitionForExist(p.getInverseProperty().getSimplified(), factory.getOWLThing());
					else 
						aux = getDefinitionForExist(p.getInverseProperty().getSimplified(), (OWLClass) filler.getComplementNNF());
					OWLClass c_p_filler = (OWLClass) aux[0];
					Boolean alreadyExists = (Boolean) aux[1];
					inclusion[indexesForNegativeUniversalsWithTransitiveSubrole[j]] = c_p_filler.getComplementNNF();
					if (!alreadyExists){
						OWLClassExpression[] exps = new OWLClassExpression[]{c_p_filler, e}; 
						finalInclusions.add(exps);

						for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){
							aux = getClassForTransitivity(t.getInverseProperty().getSimplified(), c_p_filler);
							OWLClass c_invT_cpfiller = (OWLClass) aux[0];
							alreadyExists = (Boolean) aux[1];
							exps = new OWLClassExpression[]{c_invT_cpfiller, factory.getOWLObjectAllValuesFrom(t, filler)};
							finalInclusions.add(exps);
							if (!alreadyExists){
								exps = new OWLClassExpression[]{c_invT_cpfiller, factory.getOWLObjectAllValuesFrom(t, c_invT_cpfiller.getComplementNNF())};
								finalInclusions.add(exps);
								exps = new OWLClassExpression[]{c_invT_cpfiller.getComplementNNF(), c_p_filler};
								finalInclusions.add(exps);
							}
						}
					}
				}
				else{
					throw new IllegalStateException("this was supposed to be a universal restriction " + e.toString());
				}
			}
			finalInclusions.add(inclusion);

		}

		//		//////
		//		if (anyLhsExistentialsTreated){
		//			System.out.println();
		//			for (OWLClassExpression c : inclusion)
		//				System.out.print(c.toString() + " ");
		//			System.out.println();
		//			System.out.print("becomes");
		//			for (OWLClassExpression[] newInclusion : finalInclusions){
		//				System.out.println();
		//				System.out.print("    ");
		//				for (OWLClassExpression c : newInclusion)
		//					System.out.print(c.toString() + " ");
		//			}			
		//		}
		//		//////

		return finalInclusions;
	}

	protected Object[] treatRhsUniversalsForTransitivity(
//	protected Set<OWLClassExpression[]> treatRhsUniversalsForTransitivity(
			OWLClassExpression[] inclusion,
			Integer[] indexesForPositiveUniversalsWithTransitiveSubrole,
			int nPositiveUniversals, int nOtherNegativeDisjuncts, 
			int nNegatedAtomicClasses,
			Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> rolesWithTransitiveSubroles) {

		Set<OWLClassExpression[]> finalInclusions = new HashSet<OWLClassExpression[]>();
		int nNewAtomicClasses = 0;
		//		boolean anyRhsUniversalsTreated = false;

		//isolate universal restrictions with atomic fillers or not
		if (nPositiveUniversals == 1 && ((nNegatedAtomicClasses == 1 && inclusion.length == 2) || inclusion.length == 1)){
			//then not necessary to isolate because it's already in that form, either  {A->all R.B}  or  {top->all R.B}

			finalInclusions.add(inclusion);

			OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[0]]).getProperty().getSimplified();
			OWLClass filler = (OWLClass) ((OWLObjectAllValuesFrom) inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[0]]).getFiller();
			if (inclusion.length == 1){
				//then it's a range axiom and we don't need to add any extra axioms

				//				for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){
				//					
				//					anyRhsUniversalsTreated = true;
				//					
				//					boolean[] alreadyExists = new boolean[1];
				//					OWLClass c_t_filler = getClassForTransitivity(t,(OWLClass) filler, alreadyExists);
				//					finalInclusions.add(new OWLClassExpression[]{factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
				//					if (!alreadyExists[0]){
				//						finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
				//						finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), filler});
				//					}
				//				}
			}
			else{ //inclusion.length == 2
				OWLObjectComplementOf negatedAtomicClass = null;
				for (int i = 0 ; i<inclusion.length ; i++)
					if (inclusion[i].getComplementNNF() instanceof OWLClass)
						negatedAtomicClass = (OWLObjectComplementOf) inclusion[i];

				for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){
					Object[] aux = getClassForTransitivity(t,(OWLClass) filler);
					OWLClass c_t_filler = (OWLClass) aux[0];
					Boolean alreadyExists = (Boolean) aux[1];
					finalInclusions.add(new OWLClassExpression[]{negatedAtomicClass, factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
					if (!alreadyExists){
						finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
						finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), filler});
					}
				}	
			}

		}
		else if (nOtherNegativeDisjuncts > 0){//then we isolate all the rhs universals that involve superroles of a transitive role
			for (int j = 0 ; j<nPositiveUniversals ; j++){
				OWLClassExpression e = inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[j]];
				if (e instanceof OWLObjectAllValuesFrom){
					OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) e).getProperty().getSimplified();
					OWLClassExpression filler = ((OWLObjectAllValuesFrom) e).getFiller();
					
					Object[] aux = getDefinitionForUniv(p, (OWLClass) filler);
					OWLClass c_p_filler = (OWLClass) aux[0];
					Boolean alreadyExists = (Boolean) aux[1];
					inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[j]] = c_p_filler;
					if (!alreadyExists){
						finalInclusions.add(new OWLClassExpression[]{c_p_filler.getComplementNNF(), e});

						for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){
							aux = getClassForTransitivity(t,(OWLClass) filler);
							OWLClass c_t_filler = (OWLClass) aux[0];
							alreadyExists = (Boolean) aux[1];
							finalInclusions.add(new OWLClassExpression[]{c_p_filler.getComplementNNF(), factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
							if (!alreadyExists){
								finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
								finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), filler});
							}

						}
						
						nNewAtomicClasses++;
						//for each of these expressions that we find and replace by an atomic class we can now count as if that class had been there from the start 
						//when we have to decide later whether to rewrite lhs existentials or not
					}
					//if the abbreviation for {all P. Filler} had already been created then all the transitivity propagating axioms 
					//for all its transitive subroles for Filler must have already been created as well

				}
				else{
					throw new IllegalStateException("this was supposed to be a universal restriction " + e.toString());
				}
			}
		}
		else{ //then we isolate all but one
			//for now let's just choose the last one to stay
			//we could choose the one with fewer transitive subroles so that we have to add as few axioms with union as possible
			for (int j = 0 ; j<nPositiveUniversals-1 ; j++){
				OWLClassExpression e = inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[j]];
				if (e instanceof OWLObjectAllValuesFrom){
					OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) e).getProperty().getSimplified();
					OWLClassExpression filler = ((OWLObjectAllValuesFrom) e).getFiller();
					
					Object[] aux = getDefinitionForUniv(p, (OWLClass) filler);
					OWLClass c_p_filler = (OWLClass) aux[0];
					Boolean alreadyExists = (Boolean) aux[1];
					if (!alreadyExists){

						finalInclusions.add(new OWLClassExpression[]{c_p_filler.getComplementNNF(), e});

						for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){
							
							aux = getClassForTransitivity(t,(OWLClass) filler);
							OWLClass c_t_filler = (OWLClass) aux[0];
							alreadyExists = (Boolean) aux[1];
							finalInclusions.add(new OWLClassExpression[]{c_p_filler.getComplementNNF(), factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
							if (!alreadyExists){
								finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
								finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), filler});
							}

						}
						inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[j]] = c_p_filler;
						nNewAtomicClasses++;
					}
				}
				else{
					throw new IllegalStateException("this was supposed to be a universal restriction " + e.toString());
				}
		}
			//now we handle the one we haven't isolated
			if (nPositiveUniversals > 0){
				//			if (inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[nPositiveUniversals-1]] instanceof OWLObjectAllValuesFrom)
				OWLObjectPropertyExpression p = ((OWLObjectAllValuesFrom) inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[nPositiveUniversals-1]]).getProperty().getSimplified();
				OWLClassExpression filler = ((OWLObjectAllValuesFrom) inclusion[indexesForPositiveUniversalsWithTransitiveSubrole[nPositiveUniversals-1]]).getFiller();

				for (OWLObjectPropertyExpression t : rolesWithTransitiveSubroles.get(p)){

					//					anyRhsUniversalsTreated = true;

					OWLClassExpression[] copyOfInclusion = new OWLClassExpression[inclusion.length];
					for (int j = 0 ; j<inclusion.length ; j++)
						copyOfInclusion[j] = inclusion[j];
					Object[] aux = getClassForTransitivity(t,(OWLClass) filler);
					OWLClass c_t_filler = (OWLClass) aux[0];
					Boolean alreadyExists = (Boolean) aux[1];
					copyOfInclusion[indexesForPositiveUniversalsWithTransitiveSubrole[nPositiveUniversals-1]] = factory.getOWLObjectAllValuesFrom(t, c_t_filler);
					finalInclusions.add(copyOfInclusion);

					if (!alreadyExists){
						finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), factory.getOWLObjectAllValuesFrom(t, c_t_filler)});
						finalInclusions.add(new OWLClassExpression[]{c_t_filler.getComplementNNF(), filler});
					}

				}

			}
		}

		//		//////
		//		if (anyRhsUniversalsTreated){
		//			System.out.println();
		//			for (OWLClassExpression c : inclusion)
		//				System.out.print(c.toString() + " ");
		//			System.out.println();
		//			System.out.print("becomes");
		//			for (OWLClassExpression[] newInclusion : finalInclusions){
		//				System.out.println();
		//				System.out.print("    ");
		//				for (OWLClassExpression c : newInclusion)
		//					System.out.print(c.toString() + " ");
		//			}
		//		}
		//		//////

		return new Object[]{finalInclusions, nNewAtomicClasses};
	}

	protected Object[] getDefinitionForExist(
			OWLObjectPropertyExpression p, OWLClass negatedFiller) {
		Map<OWLClass, OWLClass> aux = classesDefExist.get(p.getSimplified()); 
		if (aux != null){
			OWLClass c = aux.get(negatedFiller);
			if (c != null){
				return new Object[]{c, true};
			}
			else{
				c = getFreshClass();
				aux.put(negatedFiller, c);
				return new Object[]{c, false};
			}
		}
		else{
			aux = new HashMap<OWLClass, OWLClass>();
			OWLClass c = getFreshClass();
			aux.put(negatedFiller, c);
			classesDefExist.put(p.getSimplified(), aux);
			return new Object[]{c, false};
		}
	}
	protected Object[] getDefinitionForUniv(
			OWLObjectPropertyExpression p, OWLClass negatedFiller) {
		Map<OWLClass, OWLClass> aux = classesDefUniv.get(p.getSimplified()); 
		if (aux != null){
			OWLClass c = aux.get(negatedFiller);
			if (c != null){
				return new Object[]{c, true};
			}
			else{
				c = getFreshClass();
				aux.put(negatedFiller, c);
				return new Object[]{c, false};
			}
		}
		else{
			aux = new HashMap<OWLClass, OWLClass>();
			OWLClass c = getFreshClass();
			aux.put(negatedFiller, c);
			classesDefUniv.put(p.getSimplified(), aux);
			return new Object[]{c, false};
		}
	}
	public static void resetFreshClassCounters(){
		freshClassCounter = 0;
		freshRangeIntegClassCounter = 0;
	}
	protected OWLClass getFreshClass(){
		return factory.getOWLClass(IRI.create("internal:def#transEncoding"+(freshClassCounter++)));
	}
	protected Object[] getClassForTransitivity(
			OWLObjectPropertyExpression p, OWLClass filler) {
		Map<OWLClass, OWLClass> aux = classesToEncodeTransitivityStandard.get(p.getSimplified()); 
		if (aux != null){
			OWLClass c = aux.get(filler);
			if (c != null){
				return new Object[]{c, true};
			}
			else{
				c = getFreshClass();
				aux.put(filler, c);
				return new Object[]{c, false};
			}
		}
		else{
			aux = new HashMap<OWLClass, OWLClass>();
			OWLClass c = getFreshClass();
			aux.put(filler, c);
			classesToEncodeTransitivityStandard.put(p.getSimplified(), aux);
			return new Object[]{c, false};
		}
	}
	protected Object[] getClassForTransitivityDisjointness(
			OWLObjectPropertyExpression p, OWLClass filler) {
		Map<OWLClass, OWLClass> aux = classesToEncodeTransitivityDisjointness.get(p.getSimplified()); 
		if (aux != null){
			OWLClass c = aux.get(filler);
			if (c != null){
				return new Object[]{c, true};
			}
			else{
				c = getFreshClass();
				aux.put(filler, c);
				return new Object[]{c, false};
			}
		}
		else{
			aux = new HashMap<OWLClass, OWLClass>();
			OWLClass c = getFreshClass();
			aux.put(filler, c);
			classesToEncodeTransitivityDisjointness.put(p.getSimplified(), aux);
			return new Object[]{c, false};
		}
	}


	protected void computeTransitiveClosureOfRoleHierarchy(){

		boolean flag = true;
		while (flag) {
			flag = false;
			for (Entry<OWLObjectPropertyExpression,Set<OWLObjectPropertyExpression>> entry : roleHierarchy.entrySet()) {
				OWLObjectPropertyExpression p = entry.getKey();
				Set<OWLObjectPropertyExpression> superRolesCopy = new HashSet<OWLObjectPropertyExpression>(entry.getValue());
				for (OWLObjectPropertyExpression s : superRolesCopy){
					Set<OWLObjectPropertyExpression> moreSuperRoles = roleHierarchy.get(s);
					if (moreSuperRoles != null && entry.getValue().addAll(moreSuperRoles))
						flag = true;
				}
				if (flag && nonSimpleRoles.contains(p.getNamedProperty()))
					for (OWLObjectPropertyExpression q : entry.getValue())
						nonSimpleRoles.add(q.getNamedProperty());
			}
		}
		transitiveClosureOfRoleHierarchyComputed = true;
	}

	protected static int freshRangeIntegClassCounter = 0;
	int nRecycled = 0;
	protected Map<OWLObjectPropertyExpression, Map<OWLClassExpression, OWLClass>> rangeIntegrationClassMap = new HashMap<OWLObjectPropertyExpression, Map<OWLClassExpression,OWLClass>>();
	protected Object[] getFreshRangeIntegrationClass(OWLObjectPropertyExpression p , OWLClassExpression filler){
		Map<OWLClassExpression, OWLClass> aux = rangeIntegrationClassMap.get(p);
		if (aux != null){
			OWLClass def = aux.get(filler); 
			if (def != null){
				nRecycled++;
				return new Object[]{def, true};
			}
			else{
				def = factory.getOWLClass(IRI.create("internal:def#rangeIntegClass" + (freshRangeIntegClassCounter++)));
				aux.put(filler, def);
				return new Object[]{def, false};
			}
		}
		else{
			OWLClass def = factory.getOWLClass(IRI.create("internal:def#rangeIntegClass" + (freshRangeIntegClassCounter++)));
			aux = new HashMap<OWLClassExpression, OWLClass>();
			aux.put(filler, def);
			rangeIntegrationClassMap.put(p, aux);
			return new Object[]{def, false};
		}
	}
	//	protected int freshDomainClassCounter = -1;
	//	protected OWLClass getFreshDomainClass(){
	//		freshDomainClassCounter++;
	//		return factory.getOWLClass(IRI.create("internal:def#domainClass" + freshDomainClassCounter));
	//	}

	protected void completeRangeMapWithRoleHierarchy() {

		//when registering domain and range axioms we have stored all the info in the domainMap
		//now we will transfer this info to the rangeMap as well, and here we will also get the information that the role hierarchy gives

		//we are going to keep a copy of everything domain-wise, and also range-wise
		//the difference between the two will be that, for the domain, we will just keep, for each propertyExpression, a list of the 
		//classes stated as their domain or as the range of their inverse - without using the transitive closure of the role hierarchy;
		//for the range, we take the list gathered for the domain of the inverse, and if it contains more than one class
		//we will introduce an alias X_r specific for role r, and axioms X_r -> A for each class A in the corresponding list. 

		for (Entry<OWLObjectPropertyExpression, Set<OWLClass>> entry : rangeMap.entrySet()){
			OWLObjectPropertyExpression p = entry.getKey(); 
			OWLObjectPropertyExpression pInv = p.getInverseProperty().getSimplified();
			if (domainMap.containsKey(pInv))
				domainMap.get(pInv).addAll(entry.getValue());
			else
				domainMap.put(pInv, entry.getValue());
		}

		if (!transitiveClosureOfRoleHierarchyComputed)
			computeTransitiveClosureOfRoleHierarchy();

		for (Entry<OWLObjectPropertyExpression, Set<OWLClass>> entry : rangeMap.entrySet()){
			OWLObjectPropertyExpression p = entry.getKey();
			if (!nonSimpleRoles.contains(p.getNamedProperty())){
				//if p is non simple then we will have to include its range axiom anyway
				//furthermore, by definition all its superproperties are also non-simple so we have to include their range axioms too 
				Set<OWLObjectPropertyExpression> aux = roleHierarchy.get(p);
				if (aux != null)
					for (OWLObjectPropertyExpression q : aux){
						if (!nonSimpleRoles.contains(q.getNamedProperty())){
							//if q is non simple then we will have to include its range axiom anyway so no point in introducing more noise
							Set<OWLClass> aux2 = rangeMap.get(q);
							if (aux2 != null)
								entry.getValue().addAll(aux2);
						}
					}
			}
		}
		//Instead of adding a fresh class for the range that points to all the ranges, we just keep the whole list
		//and only introduce fresh classes when we actually replace the filler in the rhs existential restriction
	}

	public List<OWLClassExpression[]> handleRangeDomainAndSymmetricRoleAxioms(
			List<OWLClassExpression[]> conceptInclusions,
			boolean integrateRangesInRhsExistentials) {
		List<OWLClassExpression[]> updatedInclusions = new LinkedList<OWLClassExpression[]>();
		if (integrateRangesInRhsExistentials){
			completeRangeMapWithRoleHierarchy();

			//first locate the nonSimple Properties and add their range and domain axioms directly
			//since these range cannot be integrated in GCIs, and these roles can't always be detected as generating  
			for (OWLObjectProperty p : nonSimpleRoles){
				Set<OWLClass> rangeSet = rangeMap.get(p);
				if (rangeSet != null)
					for (OWLClass range : rangeSet){
						OWLObjectAllValuesFrom allPropertyRange = factory.getOWLObjectAllValuesFrom(p, range);
						updatedInclusions.add(new OWLClassExpression[] { allPropertyRange });						
					}

				Set<OWLClass> domainSet = domainMap.get(p);
				if (domainSet != null)
					for (OWLClass dom : domainSet){
						OWLObjectAllValuesFrom allPropertyNothing = factory.getOWLObjectAllValuesFrom(p, factory.getOWLNothing());
						updatedInclusions.add(new OWLClassExpression[] { dom, allPropertyNothing });						
					}
			}


			//loop through all the given inclusions adding the necessary information for ranges - for simple roles
			//and find generating roles as we go
			//and also gather the necessary information to decide if we need to keep the symmetric role axioms or not - in case there are any

			canIgnoreSymmetricRoleAxioms = true;

			while (!conceptInclusions.isEmpty()){
				OWLClassExpression[] inclusion = conceptInclusions.remove(0);
				OWLClassExpression[] newInclusion = new OWLClassExpression[inclusion.length];
				for (int i = 0 ; i < inclusion.length ; i++)
					//for each existential restriction for a SIMPLE role that has a range, we will get a fresh class associated to the role and filler, 
					///which should by now be atomic, since the class normalizer should have been applied to the inclusions before they get sent here
					if (inclusion[i] instanceof OWLObjectSomeValuesFrom){
						OWLObjectPropertyExpression p = ((OWLObjectSomeValuesFrom) inclusion[i]).getProperty().getSimplified();
						if (generatingRoles.add(p) && roleHierarchy.containsKey(p))
							generatingRoles.addAll(roleHierarchy.get(p));
						if (nonSimpleRoles.contains(p.getNamedProperty()))
							newInclusion[i] = inclusion[i];
						else{
							OWLClassExpression filler = ((OWLObjectSomeValuesFrom) inclusion[i]).getFiller();
							Set<OWLClass> rangeClasses = rangeMap.get(p);
							if (rangeClasses != null){
								Object[] aux = getFreshRangeIntegrationClass(p, filler);
								OWLClass def = (OWLClass) aux[0]; 
								Boolean alreadyExists = (Boolean) aux[1];
								newInclusion[i] = factory.getOWLObjectSomeValuesFrom(p, def);
								if (!alreadyExists){
									updatedInclusions.add(new OWLClassExpression[]{def.getComplementNNF(), filler});//add inclusions of def in every class in aux and also the filler
									for (OWLClass c : rangeClasses)
										updatedInclusions.add(new OWLClassExpression[]{def.getComplementNNF(), c});//add inclusions of def in every class in aux and also the filler
								}
							}
							else
								newInclusion[i] = inclusion[i];
						}
					}
					else if (inclusion[i] instanceof OWLObjectHasValue){ 
						OWLObjectPropertyExpression p = ((OWLObjectSomeValuesFrom) inclusion[i]).getProperty().getSimplified();
						if (generatingRoles.add(p) && roleHierarchy.containsKey(p))
							generatingRoles.addAll(roleHierarchy.get(p));
						if (nonSimpleRoles.contains(p.getNamedProperty()))
							newInclusion[i] = inclusion[i];
						else{
							OWLIndividual filler = ((OWLObjectHasValue) inclusion[i]).getValue();
							Set<OWLClass> rangeClasses = rangeMap.get(p);
							if (rangeClasses != null){
								
								Object[] aux = getFreshRangeIntegrationClass(p, factory.getOWLObjectOneOf(filler));
								OWLClass def = (OWLClass) aux[0];
								Boolean alreadyExists = (Boolean) aux[1];
								newInclusion[i] = factory.getOWLObjectSomeValuesFrom(p, def);
								if (!alreadyExists){
									updatedInclusions.add(new OWLClassExpression[]{def.getComplementNNF(), factory.getOWLObjectOneOf(filler)});//add inclusions of def in every class in aux and also the filler
									for (OWLClass c : rangeClasses)
										updatedInclusions.add(new OWLClassExpression[]{def.getComplementNNF(), c});//add inclusions of def in every class in aux and also the filler
								}
							}
							else
								newInclusion[i] = inclusion[i];							
						}
					}
					else if (inclusion[i] instanceof OWLObjectHasSelf){
						OWLObjectPropertyExpression p = ((OWLObjectHasSelf) inclusion[i]).getProperty().getSimplified();
						if (generatingRoles.add(p) && roleHierarchy.containsKey(p))
							generatingRoles.addAll(roleHierarchy.get(p));
						if (nonSimpleRoles.contains(p.getNamedProperty()))
							newInclusion[i] = inclusion[i];
						else{
							Set<OWLClass> rangeClasses = rangeMap.get(p);
							if (rangeClasses != null){
								OWLClass def = getFreshRangeIntegrationClassForSelf();
								newInclusion[i] = def;
								updatedInclusions.add(new OWLClassExpression[]{def.getComplementNNF(), inclusion[i]});//add inclusions of def in every class in aux and also the filler
								for (OWLClass c : rangeClasses)
									updatedInclusions.add(new OWLClassExpression[]{def.getComplementNNF(), c});//add inclusions of def in every class in aux and also the filler
							}
							else
								newInclusion[i] = inclusion[i];							
						}
					}
					else{
						newInclusion[i] = inclusion[i];
						if (!symmetricRoleAxioms.isEmpty()){
							if (inclusion[i] instanceof OWLObjectAllValuesFrom || inclusion[i] instanceof OWLObjectMaxCardinality)//if there are no inclusions of this kind we only need to "look forward" and don't need to use the symmetric role axioms
								canIgnoreSymmetricRoleAxioms = false;
						}
					}
				updatedInclusions.add(newInclusion);

			}

			if (!canIgnoreSymmetricRoleAxioms)
				otherRoleAxioms.addAll(symmetricRoleAxioms);

			// superroles of generating roles are also generating
			//should probably test that this is correctly done
			Set<OWLObjectPropertyExpression> newGeneratingRoles = generatingRoles;
			Set<OWLObjectPropertyExpression> newNewGeneratingRoles = new HashSet<OWLObjectPropertyExpression>();
			boolean goOn = true;
			while (goOn){
				for (OWLObjectPropertyExpression p : newGeneratingRoles)
					if (roleHierarchy.containsKey(p))
						newNewGeneratingRoles.addAll(roleHierarchy.get(p));
				newNewGeneratingRoles.removeAll(generatingRoles);
				goOn = generatingRoles.addAll(newNewGeneratingRoles);
			}


			//			finally, we'll add the domain axioms  - for the roles that turn out to be generating 
			//we've already added the ones for nonSimple Roles so we can skip those now
			for (OWLObjectPropertyExpression p : generatingRoles)
				if (!nonSimpleRoles.contains(p.getNamedProperty())){
					Set<OWLClass> domainSet = domainMap.get(p);
					if (domainSet != null)
						for (OWLClass dom : domainSet){
							OWLObjectAllValuesFrom allPropertyNothing = factory.getOWLObjectAllValuesFrom(p, factory.getOWLNothing());
							updatedInclusions.add(new OWLClassExpression[] { dom, allPropertyNothing });
						}					
				}
		}
		else{
			updatedInclusions = new ArrayList<OWLClassExpression[]>(conceptInclusions);
			for (Entry<OWLObjectPropertyExpression, Set<OWLClass>> entry : domainMap.entrySet()){
				OWLObjectPropertyExpression p = entry.getKey();
				for (OWLClass domain : entry.getValue()){
					OWLObjectAllValuesFrom allPropertyNothing = factory.getOWLObjectAllValuesFrom(p, factory.getOWLNothing());
					updatedInclusions.add(new OWLClassExpression[] { domain, allPropertyNothing });
				}
			}
			for (Entry<OWLObjectPropertyExpression, Set<OWLClass>> entry : rangeMap.entrySet()){
				OWLObjectPropertyExpression p = entry.getKey();
				for (OWLClass range : entry.getValue()){
					OWLObjectAllValuesFrom allPropertyRange = factory.getOWLObjectAllValuesFrom(p,range);
					updatedInclusions.add(new OWLClassExpression[] { allPropertyRange });
				}
			}

			decideIfSymmetricRoleAxiomsCanBeIgnored(conceptInclusions);

		}


		//		System.out.println(nRecycled +  " times we recycled a previously created def for some rhs existential restriction");


		//		System.out.println(" generating roles:");
		//		for (OWLObjectPropertyExpression p : generatingRoles)
		//			System.out.println(p.toString());
		//		System.out.println();

		return updatedInclusions;
	}
	protected OWLClass getFreshRangeIntegrationClassForSelf(){
		OWLClass def = factory.getOWLClass(IRI.create("internal:def#rangeIntegClass" + (freshRangeIntegClassCounter++)));
		return def;
	}
	protected void decideIfSymmetricRoleAxiomsCanBeIgnored(List<OWLClassExpression[]> conceptInclusions){
		if (!symmetricRoleAxioms.isEmpty()){
			canIgnoreSymmetricRoleAxioms = true;
			for (OWLClassExpression[] inclusion : conceptInclusions)
				for (OWLClassExpression c : inclusion)
					if (c instanceof OWLObjectAllValuesFrom || c instanceof OWLObjectMaxCardinality)
						canIgnoreSymmetricRoleAxioms = false;
			if (!canIgnoreSymmetricRoleAxioms)
				otherRoleAxioms.addAll(symmetricRoleAxioms);
		}
	}

}

