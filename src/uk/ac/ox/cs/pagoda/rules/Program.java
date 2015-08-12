package uk.ac.ox.cs.pagoda.rules;

import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.model.AnnotatedEquality;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLOntology;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.Equality;
import org.semanticweb.HermiT.model.Inequality;
import org.semanticweb.HermiT.model.InverseRole;
import org.semanticweb.HermiT.model.Variable;
import org.semanticweb.HermiT.structural.OWLClausification;
import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLObjectInverseOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.simpleETL.SimpleETL;

import uk.ac.ox.cs.pagoda.approx.KnowledgeBase;
import uk.ac.ox.cs.pagoda.approx.RLPlusOntology;
import uk.ac.ox.cs.pagoda.constraints.BottomStrategy;
import uk.ac.ox.cs.pagoda.constraints.NullaryBottom;
import uk.ac.ox.cs.pagoda.constraints.PredicateDependency;
import uk.ac.ox.cs.pagoda.hermit.DLClauseHelper;
import uk.ac.ox.cs.pagoda.owl.OWLHelper;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;
import uk.ac.ox.cs.pagoda.util.Utility_PAGOdA;

public abstract class Program implements KnowledgeBase {
	
	protected String ontologyDirectory = null;
	protected OWLOntology ontology; 
	protected DLOntology dlOntology;
	protected BottomStrategy botStrategy; 

	private String additionalDataFile = null; 
	
	protected Collection<DLClause> clauses = new LinkedList<DLClause>();
//	protected Set<DLClause> used = new HashSet<DLClause>();
	protected PredicateDependency dependencyGraph; 
	
	//byAna
	protected Set<AtomicRole> binaryPredsOnBodies = new HashSet<AtomicRole>();
	//we will register which binary predicates actually occur in the bodies of rules and will avoid 
	//adding transitivity axioms for binary predicates that do not occur in the body of any rule other 
	//than its transitivity axioms; this makes the materialisation a lot faster in some cases, and no 
	//information is being lost
	protected boolean containsEquality = false;
	//end byAna
	
	/**
	 * clone all information of another program after load()
	 * 
	 * @param program
	 */
	public void clone(Program program) {
		this.ontologyDirectory = program.ontologyDirectory; 
		this.ontology = program.ontology; 
		this.dlOntology = program.dlOntology;
		this.botStrategy = program.botStrategy; 
		this.additionalDataFile = program.additionalDataFile; 
		this.transitiveAxioms = program.transitiveAxioms;  
		this.transitiveClauses = program.transitiveClauses; 
		this.subPropChainAxioms = program.subPropChainAxioms; 
		this.subPropChainClauses = program.subPropChainClauses; 
	}
	
	public void load(OWLOntology o, BottomStrategy botStrategy) {
		this.botStrategy = botStrategy; 
		RLPlusOntology owlOntology = new RLPlusOntology(); 
		owlOntology.load(o, new NullaryBottom());
		owlOntology.simplify();

		ontology = owlOntology.getTBox(); 
		String ontologyPath = OWLHelper.getOntologyPath(ontology); 
		ontologyDirectory = ontologyPath.substring(0, ontologyPath.lastIndexOf(Utility_PAGOdA.FILE_SEPARATOR));
		clausify(); 
		
		String aboxOWLFile = owlOntology.getABoxPath();
		OWLOntology abox = OWLHelper.loadOntology(aboxOWLFile);
		OWLOntologyManager manager = abox.getOWLOntologyManager(); 
		OWLAxiom axiom; 
		for (Atom atom: dlOntology.getPositiveFacts()) {
			if ((axiom = OWLHelper.getABoxAssertion(manager.getOWLDataFactory(), atom)) != null)
				manager.addAxiom(abox, axiom); 
		}
		
		try {
			FileOutputStream out = new FileOutputStream(aboxOWLFile); 
			manager.saveOntology(abox, out);
			out.close();
		} catch (OWLOntologyStorageException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		if (!abox.isEmpty()) {
			SimpleETL rewriter = new SimpleETL(owlOntology.getOntologyIRI(), aboxOWLFile);
			try {
				rewriter.rewrite();
			} catch (Exception e) {
				e.printStackTrace();
			} 
			additionalDataFile = rewriter.getExportedFile(); 
		}
		
	}
	
	protected void clausify() {
		Configuration conf = new Configuration();
		OWLClausification clausifier = new OWLClausification(conf);
		OWLOntology filteredOntology = null;
		OWLOntologyManager manager = ontology.getOWLOntologyManager();
		try {
			filteredOntology = manager.createOntology();
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		
		transitiveAxioms = new LinkedList<OWLTransitiveObjectPropertyAxiom>();
		subPropChainAxioms = new LinkedList<OWLSubPropertyChainOfAxiom>();
		
		int noOfDataPropertyRangeAxioms = 0, noOfAxioms = 0; 
		for (OWLOntology onto: ontology.getImportsClosure())
			for (OWLAxiom axiom: onto.getAxioms()) {
				if (axiom instanceof OWLTransitiveObjectPropertyAxiom) 
					transitiveAxioms.add((OWLTransitiveObjectPropertyAxiom) axiom);
				else if (axiom instanceof OWLSubPropertyChainOfAxiom) 
					subPropChainAxioms.add((OWLSubPropertyChainOfAxiom) axiom);
				// TODO to filter out datatype axioms
				else if (axiom instanceof OWLDataPropertyRangeAxiom) {
					++noOfDataPropertyRangeAxioms; 
				}
				else {
					manager.addAxiom(filteredOntology, axiom);
				}
				
				if (axiom instanceof OWLAnnotationAssertionAxiom ||
						axiom instanceof OWLSubAnnotationPropertyOfAxiom ||
						axiom instanceof OWLDeclarationAxiom ||
						axiom instanceof OWLDataPropertyRangeAxiom); 
				else {
//					System.out.println(axiom); 
					++noOfAxioms;
				}
					
			}
		Logger_MORe.logInfo("The number of data property range axioms that are ignored: " + noOfDataPropertyRangeAxioms + "(" + noOfAxioms + ")");
		
		dlOntology = (DLOntology)clausifier.preprocessAndClausify(filteredOntology, null)[1];
		clausifier = null;
	}
	
	public String getAdditionalDataFile() {
		return additionalDataFile; 
	}

	protected LinkedList<OWLTransitiveObjectPropertyAxiom> transitiveAxioms;
	protected LinkedList<DLClause> transitiveClauses;
	
	protected LinkedList<OWLSubPropertyChainOfAxiom> subPropChainAxioms; 
	protected LinkedList<DLClause> subPropChainClauses;
	
	@Override
	public void transform() {
		for (DLClause dlClause: dlOntology.getDLClauses()) {
			DLClause simplifiedDLClause = DLClauseHelper.removeNominalConcept(dlClause);
			simplifiedDLClause = removeAuxiliaryBodyAtoms(simplifiedDLClause);
			simplifiedDLClause  = DLClauseHelper.replaceWithDataValue(simplifiedDLClause);
			convert(simplifiedDLClause);
		}

		addingTransitiveAxioms();
		addingSubPropertyChainAxioms();
		
		Collection<DLClause> botRelated = new LinkedList<DLClause>(); 
		Variable X = Variable.create("X"); 
		botRelated.add(DLClause.create(new Atom[0], new Atom[] {Atom.create(Inequality.INSTANCE, X, X)}));
		clauses.addAll(botStrategy.process(botRelated)); 
		
		if (this instanceof GeneralProgram)
			Logger_MORe.logInfo("The number of rules: " + (clauses.size() - 1));
	}
	
	protected DLClause removeAuxiliaryBodyAtoms(DLClause dlClause) {
		Collection<Atom> newBodyAtoms = new LinkedList<Atom>();
		DLPredicate p; 
		for (Atom bodyAtom: dlClause.getBodyAtoms()) {
			p = bodyAtom.getDLPredicate(); 
			if (p instanceof AtomicConcept || 
					p instanceof AtomicRole || p instanceof InverseRole ||
					p instanceof Equality || p instanceof AnnotatedEquality || p instanceof Inequality)
				newBodyAtoms.add(bodyAtom); 
				
		}
		
		if (newBodyAtoms.size() == dlClause.getBodyLength())
			return dlClause; 
		
		return DLClause.create(dlClause.getHeadAtoms(), newBodyAtoms.toArray(new Atom[0])); 
	}

	protected void addingTransitiveAxioms() {
		DLClause transitiveClause;
		Atom headAtom;
		Variable X = Variable.create("X"), Y = Variable.create("Y"), Z = Variable.create("Z");
		transitiveClauses = new LinkedList<DLClause>();
		//byAna
		Iterator<OWLTransitiveObjectPropertyAxiom> iter = transitiveAxioms.iterator();
		while (iter.hasNext()){
			OWLTransitiveObjectPropertyAxiom axiom = iter.next();
			OWLObjectPropertyExpression objExp = axiom.getProperty(); 
			headAtom = getAtom(objExp, X, Z);
			if (binaryPredsOnBodies.contains((AtomicRole) headAtom.getDLPredicate())){
				Atom[] bodyAtoms = new Atom[2];
				bodyAtoms[0] = getAtom(objExp, X, Y); 
				bodyAtoms[1] = getAtom(objExp, Y, Z); 
				transitiveClause = DLClause.create(new Atom[] {headAtom}, bodyAtoms); 
				clauses.add(transitiveClause);
				transitiveClauses.add(transitiveClause);
			}
			else{
				iter.remove();
				//need to remove the element so that the lists of transitivity axioms and clauses still match because I will traverse them in parallel later to add the correspondences. 
			}
		}
		//end byAna
//		//original
//		for (OWLTransitiveObjectPropertyAxiom axiom: transitiveAxioms) {
//			OWLObjectPropertyExpression objExp = axiom.getProperty(); 
//			headAtom = getAtom(objExp, X, Z);
//			Atom[] bodyAtoms = new Atom[2];
//			bodyAtoms[0] = getAtom(objExp, X, Y); 
//			bodyAtoms[1] = getAtom(objExp, Y, Z); 
//			transitiveClause = DLClause.create(new Atom[] {headAtom}, bodyAtoms); 
//			clauses.add(transitiveClause);
//			transitiveClauses.add(transitiveClause);
//		}
//		//endOriginal
	}
	
	private Atom getAtom(OWLObjectPropertyExpression exp, Variable x, Variable y) {
		if (exp instanceof OWLObjectProperty)
			return Atom.create(AtomicRole.create(((OWLObjectProperty) exp).toStringID()), x, y);
		OWLObjectInverseOf inverseOf; 
		if (exp instanceof OWLObjectInverseOf && (inverseOf = (OWLObjectInverseOf) exp).getInverse() instanceof OWLObjectProperty)
			return Atom.create(AtomicRole.create(((OWLObjectProperty) inverseOf).toStringID()), x, y);
		return null;
	}

	private void addingSubPropertyChainAxioms() {
		DLClause dlClause; 
		subPropChainClauses = new LinkedList<DLClause>();
		Atom headAtom;
		Iterator<OWLObjectPropertyExpression> iterExp; 
		OWLObjectPropertyExpression objExp; 
		for (OWLSubPropertyChainOfAxiom axiom: subPropChainAxioms) {
			objExp = axiom.getSuperProperty();
			List<OWLObjectPropertyExpression> objs = axiom.getPropertyChain();
			headAtom = getAtom(objExp, Variable.create("X"), Variable.create("X" + objs.size()));
			iterExp = objs.iterator();
			int index = 1; 
			Atom[] bodyAtoms = new Atom[objs.size()]; 
			bodyAtoms[0] = getAtom(iterExp.next(), Variable.create("X"), Variable.create("X1")); 
			while (index < objs.size()) {
				bodyAtoms[index] = getAtom(iterExp.next(), Variable.create("X" + index), Variable.create("X" + (index + 1)));
				++index; 
			}
			dlClause = DLClause.create(new Atom[] {headAtom}, bodyAtoms); 
			clauses.add(dlClause); 
			subPropChainClauses.add(dlClause); 
		}
	}

	@Override
	public void save() {
		try {
			BufferedWriter ruleWriter = new BufferedWriter(new OutputStreamWriter(
					new FileOutputStream(getOutputPath())));
			ruleWriter.write(toString());
			ruleWriter.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		Logger_MORe.logDebug("The rules are saved in " + getOutputPath() + "."); 
	}
	
	@Override
	public String toString() {
		return toString(clauses); 
	}
	
	public static String toString(Collection<DLClause> clauses) {
		StringBuilder sb = new StringBuilder(DLClauseHelper.toString(clauses)); 
		sb.insert(0, MyPrefixes.PAGOdAPrefixes.prefixesText()); 
		return sb.toString(); 
	}
	
	public final void convert(DLClause clause) {
		Collection<DLClause> tempClauses = convert2Clauses(clause);
		clauses.addAll(tempClauses);
		
		//byAna
		for (DLClause c : tempClauses){
			for (Atom at : c.getBodyAtoms()){
				DLPredicate pred = at.getDLPredicate();
				if (pred instanceof AtomicRole)
					binaryPredsOnBodies.add((AtomicRole) pred);
			}
			if (!containsEquality)
				if (c.getHeadAtom(0).getDLPredicate().toString().contains("==")){
					containsEquality = true;
					Logger_MORe.logDebug("# contains equality");
				}
		}
		//end byAna
	}
	
	public abstract Collection<DLClause> convert2Clauses(DLClause clause);

	public abstract String getOutputPath();
	
	
	public OWLOntology getOntology() {
		return ontology;
	}
	
	public Collection<DLClause> getClauses() {
		Logger_MORe.logInfo(clauses.size() + " dl clauses");
		return clauses;
	}
	
	public Collection<DLClause> getClauses(DLClause queryClause) {
//		if (true) return new HashSet<DLClause>(clauses); 
		Set<DLPredicate> predicates = new HashSet<DLPredicate>();
		predicates.addAll(dependencyGraph.collectPredicate(queryClause.getBodyAtoms())); 
		
		Set<DLPredicate> dependence = new HashSet<DLPredicate>(); 
		for (DLPredicate predicate: predicates)
			dependence.addAll(dependencyGraph.getAncesters(predicate));
		
		Collection<DLClause> relevantClauses = new LinkedList<DLClause>(); 
		for (DLClause clause: clauses) {
			if (relevant(clause, dependence))
				relevantClauses.add(clause);
			
		}
		return relevantClauses; 
	}

	private boolean relevant(DLClause clause, Set<DLPredicate> set) {
		for (DLPredicate p: dependencyGraph.collectPredicate(clause.getHeadAtoms()))
			if (set.contains(p))
				return true;
		return false; 
	}

	public PredicateDependency buildDependencyGraph() {
		if (dependencyGraph == null)
			return dependencyGraph = new PredicateDependency(clauses);  
		else 
			return dependencyGraph; 
	}
	
	public void getDependencyGraph(PredicateDependency g) {
		dependencyGraph = g; 
	}
	
	public final String getDirectory() {
		return Utility_PAGOdA.TempDirectory; 
	}
	
	//byAna
	public boolean containsEquality(){
		return containsEquality;
	}
}
