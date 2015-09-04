package org.semanticweb.more.pagoda;

import java.io.File;
import java.util.Set;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;

import org.semanticweb.more.util.Logger_MORe;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntology;

import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.ox.cs.pagoda.query.ClassificationQueryType;
import uk.ac.ox.cs.pagoda.query.GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly;
import uk.ac.ox.cs.pagoda.query.GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality;
import uk.ac.ox.cs.pagoda.util.MyPrefixes;

public class PAGOdAClassificationManager_parallel extends PAGOdAClassificationManager {

	//only the RL program is done in parallel
	
	public PAGOdAClassificationManager_parallel(OWLOntology o, Set<OWLClass> classesToClassify, boolean multiStage, ClassificationQueryType qType){
		super(o,classesToClassify, multiStage, qType);
	}

	@Override
	public boolean preprocess() {//returns true if the ontology is already fully classified, false otherwise
		t.reset(); 
		Logger_MORe.logInfo("Preprocessing ontology for classification... ");
		String name = "instantiation ABox", datafile = importedData.toString(); 

		ForkJoinPool executor = new ForkJoinPool();
		
		LowerStoreLauncher lowerLauncher = new LowerStoreLauncher(name, datafile);
		
		if (lazyUpperStore != null) {
			LazyUpperStoreLauncher lazyLauncher = new LazyUpperStoreLauncher(name, datafile);
			
			executor.execute(lowerLauncher);
			executor.execute(lazyLauncher);
			lowerLauncher.join();
			lowerStore.importRDFData("skolem data", aBoxManager.skolemABox_fileName);
			lowerStore.materialise("el program", new File(program.getELprogram().getOutputPath()), false);
			updateUnsatisfiableClasses();
			lazyLauncher.join();
			lazyGap = new GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality(lazyUpperStore, lowerStore);
			lazyUpperStore.materialiseMultiStage(program, aBoxManager.skolemABox_fileName, lazyGap, lowerStore, true);

			//before launching the trackingStore check if the gap is empty
			if (lazyGap.getNamedIndividualsWithGap().isEmpty()){
				return true;
			}
			else{
				individualsWithContradictionsInLazyStore = lazyGap.getNamedInstancesOfNothing();
				individualsWithGap = lazyGap.getNamedIndividualsWithGap();
				if (individualsWithGap.size() < classesToClassify.size()){
					updateClassesWithGapFromIndividualsWithGap();
					aBoxManager.updateInstantiationABox(individualsWithGap);
					indManager.updateActiveIndexes(individualsWithGap);
					updateUpperProgramWithGap(ModuleType.BOT);
				}
				else if (!unsatisfiableClasses.isEmpty())//moved here from after updatingUnsatClasses
					aBoxManager.updateInstantiationABox(classesToClassify);

				trackingStore.importRDFData(name, datafile);
				gap = new GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality(trackingStore, lowerStore); 
				trackingStore.materialise(program, aBoxManager.skolemABox_fileName, gap, lowerStore, indManager, false);

				//if there are any contradictions in the lazyUpperStore then we need to consider the predicatesWithGap given by the trackingStore
				if (individualsWithContradictionsInLazyStore.isEmpty()){
					//if there are no contradictions in the lazyUpperStore then the predicates with gap in the lazyUpperStore (plus owl:Nothing!!) are the only ones we need to consider
					predicatesWithGap = lazyGap.getPredicatesWithGap();
					predicatesWithGap.add(MyPrefixes.PAGOdAPrefixes.expandText("owl:Nothing"));
				}
				else
					predicatesWithGap = gap.getPredicatesWithGap();
				updateUpperProgramWithGap(ModuleType.TOP);
				gap.clear();//this only clears the iterator inside the gap, everything else remains intact so we can still access it
				lazyGap.clear();
				return false;
			}
		}
		else{
			TrackingStoreLauncher trackingLauncher = new TrackingStoreLauncher(name, datafile);
			
			executor.execute(lowerLauncher);
			executor.execute(trackingLauncher);
			lowerLauncher.join();
			lowerStore.importRDFData("skolem data", aBoxManager.skolemABox_fileName);
			lowerStore.materialise("el program", new File(program.getELprogram().getOutputPath()), false);
			trackingLauncher.join();
			gap = new GapByStore4ID_registerInfoAboutInstantiationIndividualsOnly_supportingEquality(trackingStore, lowerStore); 
			trackingStore.materialise(program, aBoxManager.skolemABox_fileName, gap, lowerStore, indManager, true);
			
			predicatesWithGap = gap.getPredicatesWithGap(); 
			individualsWithGap = gap.getNamedIndividualsWithGap();
			if (individualsWithGap.size() < classesToClassify.size()){
				updateClassesWithGapFromIndividualsWithGap();
				aBoxManager.updateInstantiationABox(individualsWithGap);
				indManager.updateActiveIndexes(individualsWithGap);
				updateUpperProgramWithGap(ModuleType.STAR);
			}
			gap.clear();
			return false;
		}
	}

	class LowerStoreLauncher extends ForkJoinTask<Object>{

		/**
		 * 
		 */
		private static final long serialVersionUID = -6290155134070188986L;
		String name;
		String datafile;

		public LowerStoreLauncher(String name, String datafile){
			this.name = name;
			this.datafile = datafile;
		}


		@Override
		protected boolean exec() {
			lowerStore.importRDFData(name, datafile);
			lowerStore.materialise("rl program", new File(program.getRLprogram().getOutputPath()));
			return true;
		}

		@Override
		public Object getRawResult() {
			return null;
		}

		@Override
		protected void setRawResult(Object arg0) { }

	}

	class LazyUpperStoreLauncher extends ForkJoinTask<Object>{

		/**
		 * 
		 */
		private static final long serialVersionUID = -4948868182713198490L;
		String name;
		String datafile;

		public LazyUpperStoreLauncher(String name, String datafile){
			this.name = name;
			this.datafile = datafile;
		}


		@Override
		protected boolean exec() {
			lazyUpperStore.importRDFData(name, datafile);
			lazyUpperStore.materialise("rl program", new File(program.getRLprogram().getOutputPath()));
			return true;
		}

		@Override
		public Object getRawResult() {
			return null;
		}

		@Override
		protected void setRawResult(Object arg0) { }

	}

	class TrackingStoreLauncher extends ForkJoinTask<Object>{

		/**
		 * 
		 */
		private static final long serialVersionUID = -4948868182713198490L;
		String name;
		String datafile;

		public TrackingStoreLauncher(String name, String datafile){
			this.name = name;
			this.datafile = datafile;
		}


		@Override
		protected boolean exec() {
			trackingStore.importRDFData(name, datafile);
			trackingStore.materialise("rl program", new File(program.getRLprogram().getOutputPath()));
			return true;
		}

		@Override
		public Object getRawResult() {
			return null;
		}

		@Override
		protected void setRawResult(Object arg0) { }

	}
}