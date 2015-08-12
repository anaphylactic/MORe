package org.semanticweb.more.reasoner;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLProperty;



public class ListProcessor {

	//We try not to remove roles unless strictly necessary
	
	public Set<OWLEntity> getMinimalCombination(List<List<Set<OWLEntity>>> possibilities, int upperBound){
		/*
		 * For each (outer list: over axioms) axiom that we need to make local, we probably have
		 * a few different possibilities (inner list: over different possibilities for a given 
		 * axiom) as to which set of symbols we need to remove from the harmlessSignature.
		 * 
		 * We follow a greedy strategy: first, we look at the the possibilities for those axioms 
		 * for which there is only one way to proceed - we assume that these are precisely the 
		 * first elements in the list, (better to make all deterministic decisions before we start 
		 * making nondeterministic ones) so one must make sure that is the case before calling this method. 
		 * Then, we go through the remaining elements in whatever order they come and keep the 
		 * "solution" that adds fewer symbols to the accumulator while still not adding any roles.
		 */

		//plain greedy algorithm
		//System.out.println("getMinimalCombination");
		//System.out.println( possibilities.size() + " axioms need to make local");		
		Set<OWLEntity> accumulator = new HashSet<OWLEntity>();
		for (List<Set<OWLEntity>> solutionsForSomeAxiom : possibilities){//does this go through the list in its natural order??
			accumulator.addAll(addsFewest(solutionsForSomeAxiom, accumulator, upperBound));
		}
		return accumulator;
	}
	
	
	public Set<OWLEntity> addsFewest(List<Set<OWLEntity>> list, Set<OWLEntity> set, int upperBound){
		//System.out.println("addsFewest");
		Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
		if (list.size() > 0){
			int index = 0;
			int bestIndexSoFar = 0;
			int adds;
			int chosenAdds;
			int minNoRolesSoFar;
			int roles;
			chosenAdds = upperBound;
			minNoRolesSoFar = upperBound;
			for (Set<OWLEntity> possibility : list){
				adds = 0;
				roles = 0;
				for (OWLEntity symbol : possibility){
					if (!set.contains(symbol)){
						adds ++;
					}
					if (symbol instanceof OWLProperty<?,?>){
						roles++;
					}
				}
				
				//System.out.println("would add " + adds);
				if (roles < minNoRolesSoFar || (roles == minNoRolesSoFar  &&  adds < chosenAdds)){
					minNoRolesSoFar = roles;
					chosenAdds = adds;
					bestIndexSoFar = index;
				}
				index++;
			}
			auxSet = list.get(bestIndexSoFar); 
			//System.out.println(bestIndexSoFar);
		}
		return auxSet; 
	}
		
	
	//unlike the first two, this procedure is not greedy but optimal
	public Set<OWLEntity> getBestCombination(List<Set<OWLEntity>> list1, List<Set<OWLEntity>> list2, int upperBound){
		//System.out.println("getBestCombination");
		Set<OWLEntity> aux = new HashSet<OWLEntity>();
		int i1 = 0;
		int i2 = 0;
		int best1 = 0;
		int best2 = 0;	
		int chosenAdds = upperBound;
		int minNoRolesSoFar = upperBound;
		int roles;
		for (Set<OWLEntity> s1 : list1){
			i2 = 0;
			for(Set<OWLEntity> s2 : list2){
				aux = new HashSet<OWLEntity>();
				aux.addAll(s1);
				aux.addAll(s2);
				roles = countRoles(aux);
				
				if ((roles < minNoRolesSoFar) || (roles == minNoRolesSoFar  &&  aux.size() < chosenAdds)){
					chosenAdds = aux.size();
					minNoRolesSoFar = roles;
					best1 = i1;
					best2 = i2;
				}
				i2++;
			}
			i1++;
		}
		aux = new HashSet<OWLEntity>();
		aux.addAll(list1.get(best1));
		aux.addAll(list2.get(best2));
		return aux;
	}
	
	
	public int countRoles(Set<OWLEntity> symbols){
		int nRoles = 0;
		for (OWLEntity symbol : symbols){
			if (symbol instanceof OWLProperty<?,?>){
				nRoles++;
			}
		}
		return nRoles;
	}
	


	public List<Set<OWLEntity>> getAllCombinations(List<List<Set<OWLEntity>>> solsForEachDisjunct, boolean useEvery){
		List<Set<OWLEntity>> commonSolutions = new LinkedList<Set<OWLEntity>>();
		
		//we need to remove every empty list in solsForEachDisjunct
		List<List<Set<OWLEntity>>> filteredSolsForEachDisjunct = new LinkedList<List<Set<OWLEntity>>>();
		for (List<Set<OWLEntity>> list : solsForEachDisjunct){
			if (!list.isEmpty()){
				filteredSolsForEachDisjunct.add(list);
			}
		}
		int size = filteredSolsForEachDisjunct.size();
		
		if (useEvery){
			//how many solutions do we get? total
			int total = 1;
			for (List<Set<OWLEntity>> solsForOneDisjunct : filteredSolsForEachDisjunct){
				total = total * solsForOneDisjunct.size();
			}
			if (total < 100){
				for (int i=0 ; i<total ; i++){
					commonSolutions.add(new HashSet<OWLEntity>());
				}
				List<Set<OWLEntity>> solsForOneDisjunct;
				
				int walker; //walks along the list commonSolutions filling in the solutions
				int blockSize;
				int index;
				for (int i=0 ; i<size ; i++){
					solsForOneDisjunct = filteredSolsForEachDisjunct.get(i);
					blockSize = 1;
					for (int k=i+1 ; k<size ; k++){
						blockSize = blockSize*filteredSolsForEachDisjunct.get(k).size();
					}
					walker = 0;
					index = 0;
					while (walker < total){
						commonSolutions.get(walker).addAll(solsForOneDisjunct.get(index));
						walker++;
						if (walker % blockSize == 0){
							index = (index + 1) % solsForOneDisjunct.size();
						}
					}
				}	
			}
			else{//if there are too many possible combinations, then we will get only one in a greedy way
				Set<OWLEntity> greedySolution = new HashSet<OWLEntity>();
				int upperBound = 0;
				for (List<Set<OWLEntity>> solsForOneDisjunct : filteredSolsForEachDisjunct){
					for (Set<OWLEntity> singleSol : solsForOneDisjunct){
						upperBound = upperBound + singleSol.size();
					}
				}
				
				for (List<Set<OWLEntity>> solsForOneDisjunct : filteredSolsForEachDisjunct){
					greedySolution.addAll(addsFewest(solsForOneDisjunct, greedySolution, upperBound));
				}
				commonSolutions.add(greedySolution);
			}
		}
		else{
			List<List<Set<OWLEntity>>> auxList;
			for (int i=0 ; i<size ; i++){
				auxList = new LinkedList<List<Set<OWLEntity>>>();
				for (int j=0 ; j<size ; j++){
					if (i!=j){
						auxList.add(solsForEachDisjunct.get(j));
					}
				}
				commonSolutions.addAll(getAllCombinations(auxList, true));
			}
		}
		return commonSolutions;
	}

}
	
