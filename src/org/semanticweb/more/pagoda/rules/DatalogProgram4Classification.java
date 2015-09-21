package org.semanticweb.more.pagoda.rules;
import java.util.Set;

import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.owlapi.model.OWLOntology;

import uk.ac.ox.cs.pagoda.constraints.BottomStrategy;
import uk.ac.ox.cs.pagoda.constraints.PredicateDependency;
import uk.ac.ox.cs.pagoda.constraints.UnaryBottom;
import uk.ac.ox.cs.pagoda.rules.GeneralProgram;
import uk.ac.ox.cs.pagoda.rules.LowerDatalogProgram;


public class DatalogProgram4Classification{// extends DatalogProgram{ because of how the constructor works in DatalogProgram I can't extend it because it would construct all the programs in the environment variables before I've had time to make them instances of Classification specific classes 

	UpperDatalogProgram4Classification upperProgram = new UpperDatalogProgram4Classification(); 
//	LowerDatalogProgram4Classification lowerProgramRL;
	LowerDatalogProgram4Classification lowerProgram;
	//it is ok to consider only one lower program, namely one corresponding to the OWL 2 EL part of the ontology 
	//(excluding reflexivity axioms and axioms mentioning individuals), and not bothering with the RL program:
	//we could not include any axioms mentioning individuals in the RL program because, since our ABox is synthetic, 
	//this could have unexpected effects; furthermore, MORe ignores any ABox that the input ontology may contain, so 
	//there can be no binary predicate assertions in the initial dataset, therefore the RL program would not produce 
	//anything that the EL program is not going to produce anyway
	GeneralProgram program = new GeneralProgram();
	
	BottomStrategy upperBottom; 
	
	public DatalogProgram4Classification(OWLOntology o, boolean useKarma) {
		upperProgram = new UpperDatalogProgram4Classification(); 
		program = new GeneralProgram();
		lowerProgram = new LowerDatalogProgram4Classification();
		init(o); 
	}
	

	private void init(OWLOntology o) {
		upperProgram.load(o, upperBottom = new UnaryBottom());
		lowerProgram.loadRestrictedELontology(o);
		program.clone(upperProgram);
		
		upperProgram.transform();
		lowerProgram.transform();
		program.transform();
		
		program.buildDependencyGraph();
		PredicateDependency graph = upperProgram.buildDependencyGraph(); 
		lowerProgram.setDependencyGraph(graph);
	}

	public LowerDatalogProgram getLower() {
		return lowerProgram; 
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
