package org.semanticweb.more.pagoda.rules;
import java.util.Collection;
import java.util.Set;

import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLOntology;
import org.semanticweb.owlapi.model.OWLOntology;

import uk.ac.ox.cs.pagoda.constraints.BottomStrategy;
import uk.ac.ox.cs.pagoda.constraints.PredicateDependency;
import uk.ac.ox.cs.pagoda.constraints.UnaryBottom;
import uk.ac.ox.cs.pagoda.rules.GeneralProgram;
import uk.ac.ox.cs.pagoda.rules.LowerDatalogProgram;


public class DatalogProgram4Classification{// extends DatalogProgram{ because of how the constructor works in DatalogProgram I can't extend it because it would construct all the programs in the environment variables before I've had time to make them instances of Classification specific classes 

	UpperDatalogProgram4Classification upperProgram = new UpperDatalogProgram4Classification(); 
	LowerDatalogProgram4Classification lowerProgramRL; //OWL 2 RL
	//if there are no nominals then this program won't mention any roles in heads of rules so there is not need to cahnge anything - regarding adding Abox assertions instead of rules, or regarding propagating axioms either. 
	//if there are nominals then we shouldn't really take them in the lower bound anyway because, since our ABox is synthetic, this could have unexpected effects - this would imply modifying the lower program's approximator so that those are ignored too.
	LowerDatalogProgram4Classification lowerProgramEL;//this will be the OWL 2 EL one
	GeneralProgram program = new GeneralProgram();
	
	BottomStrategy upperBottom; 
	
	public DatalogProgram4Classification(OWLOntology o, boolean useKarma) {
		upperProgram = new UpperDatalogProgram4Classification(); 
		program = new GeneralProgram();
		lowerProgramRL = new LowerDatalogProgram4Classification("RL");
		if (!useKarma)
			lowerProgramEL = new LowerDatalogProgram4Classification("EL");
		init(o); 
	}
	

	private void init(OWLOntology o) {
//		upperProgram.load(o, upperBottom = new UpperUnaryBottom());//this is what Yujiao had
		upperProgram.load(o, upperBottom = new UnaryBottom());//this was commented in Yujiao's code
		lowerProgramRL.clone(upperProgram);
		if (lowerProgramEL != null)
			lowerProgramEL.loadRestrictedELontology(o);
		program.clone(upperProgram);
//		program.botStrategy = new UnaryBottom(); 
		
		upperProgram.transform();
		lowerProgramRL.transform();
		if (lowerProgramEL != null)
			lowerProgramEL.transform();
		program.transform();
		
		program.buildDependencyGraph();
		PredicateDependency graph = upperProgram.buildDependencyGraph(); 
		lowerProgramRL.setDependencyGraph(graph);
		if (lowerProgramEL != null)
			lowerProgramEL.setDependencyGraph(graph);
	}

//	public LowerDatalogProgram getLower() {
//		return lowerProgramRL; 
//	}

	public LowerDatalogProgram getRLprogram() {
		return lowerProgramRL; 
	}

	public LowerDatalogProgram getELprogram() {
		return lowerProgramEL; 
	}

	public UpperDatalogProgram4Classification getUpper() {
		return upperProgram; 
	}
	
	public GeneralProgram getGeneral() {
		return program; 
	}
	
	public String getAdditionalDataFile() {
		return upperProgram.getAdditionalDataFile();
	}

	public BottomStrategy getUpperBottomStrategy() {
		return upperBottom;
	}

	
	public Set<Atom> getAdditionalABoxFacts(){
		return upperProgram.getAdditionalFacts();

	}


	public void updateUpperProgram(OWLOntology starModule) {
		upperProgram = new UpperDatalogProgram4Classification(); 
		
		upperProgram.load(starModule, upperBottom);
		upperProgram.transform();
		upperProgram.buildDependencyGraph(); //do I need this??
	}

}
