package org.semanticweb.more.pagoda;

import java.io.File;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.Set;

import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.more.util.PrintingUtility;
import org.semanticweb.owlapi.model.OWLClass;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;

public class ABoxManager {

	IndividualManager indManager;
	public final String instantiationABox_fileName = Utility_PAGOdA.TempDirectory + "instantiationABox.ttl";
	public final String skolemABox_fileName = Utility_PAGOdA.TempDirectory + "skolemABox.ttl";

	public ABoxManager(IndividualManager iManager){
		indManager = iManager;
	}

	public String createInstantiationABox(Set<OWLClass> signature){
		PrintWriter facts = null;
		try{
			facts = new PrintWriter(new File(instantiationABox_fileName));

			for (OWLClass c : signature){
				Individual i = indManager.getInstanceIndividual(c, true);
				PrintingUtility.print(facts, c, i);
			}
			//now we will retrieve from the individualManager assertions of top for all the individuals created  
			//that way we will get them without redundance
			indManager.printTopFactsForAllIndividuals(facts);
			facts.close();
			return instantiationABox_fileName;
		}
		catch (Exception e){
			e.printStackTrace();
		}
		finally{
			if (facts != null)
				facts.close();
		}
		return null;
	}
	public String updateInstantiationABox(Collection<String> individuals){
		PrintWriter facts = null;
		try{
			facts = new PrintWriter(new File(instantiationABox_fileName));
			OWLClass top = new OWLDataFactoryImpl().getOWLThing();
			for (String i : individuals){
				OWLClass c = indManager.getClass4Individual(i);
				PrintingUtility.print(facts, c, i);
				PrintingUtility.print(facts, top, i);	//we also print assertions of top for the individuals provided
			}
			facts.close();
			return instantiationABox_fileName;
		}
		catch (Exception e){
			e.printStackTrace();
		}
		finally{
			if (facts != null)
				facts.close();
		}
		return null;
	}
	public String updateInstantiationABox(Set<OWLClass> signature){
		PrintWriter facts = null;
		try{
			facts = new PrintWriter(new File(instantiationABox_fileName));
			
			OWLClass top = new OWLDataFactoryImpl().getOWLThing();
			for (OWLClass c : signature){
				Individual i = indManager.getInstanceIndividual(c, true);
				PrintingUtility.print(facts, c, i);
				PrintingUtility.print(facts, top, i);//this will not introduce redundant facts because, unlike with the modules, here we always have a different instantiation indivual for each class
			}
			facts.close();
			return instantiationABox_fileName;
		}
		catch (Exception e){
			e.printStackTrace();
		}
		finally{
			if (facts != null)
				facts.close();
		}
		return null;
	}


	
	public String createSkolemABox(Set<Atom> additionalFacts){
		PrintWriter facts = null;
		try{
			facts = new PrintWriter(new File(skolemABox_fileName));
			for (Atom at : additionalFacts)
				PrintingUtility.print(facts, (AtomicConcept) at.getDLPredicate(), (Individual) at.getArgument(0));
			facts.close();
			return skolemABox_fileName;
		}
		catch (Exception e){
			e.printStackTrace();
		}
		finally{
			if (facts != null)
				facts.close();
		}
		return null;
	}
	public String updateSkolemABox(Set<Atom> additionalFacts){
		PrintWriter facts = null;
		try{
			facts = new PrintWriter(new File(skolemABox_fileName));
			for (Atom at : additionalFacts)
				PrintingUtility.print(facts, (AtomicConcept) at.getDLPredicate(), (Individual) at.getArgument(0));
			facts.close();
			return skolemABox_fileName;
		}
		catch (Exception e){
			e.printStackTrace();
		}
		finally{
			if (facts != null)
				facts.close();
		}
		return null;
	}
}
