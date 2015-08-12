package org.semanticweb.more.reasoner;

import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLEntity;

/**
 * We use this class to gather information about some axiom or class found in
 * some method so that we can return the whole lot of information at once. We
 * may want to know if an axiom is local - "is" will give us the answer to that.
 * If the axiom is not local, then "canMake" will tell us whether it is possible
 * to make it local and, if it is, then solutions will give us a list of
 * possible sets of symbols that we can take out of the external signature to
 * make it local. We may also want to know whether a class is locally "top"
 * (resp. "bottom") or not. Similarly, "is" will give us the answer to that, and
 * if this answer is no then "canMake" will tell us if there is any way to fix
 * that, and if there is one then "solutions" will give us a few options.
 */
public class LocalityInfo {

	private boolean is;
	private boolean canMake;
	private List<Set<OWLEntity>> solutions;

	/**
	 * this method does...
	 * 
	 * @param is
	 * @param canMake
	 * @param solutions
	 */
	public LocalityInfo(boolean is, boolean canMake,
			List<Set<OWLEntity>> solutions) {
		this.is = is;
		this.canMake = canMake;
		this.solutions = solutions;
	}

	public boolean is() {
		return is;
	}

	public boolean canMake() {
		return canMake;
	}

	public List<Set<OWLEntity>> getSolutions() {
		return solutions;
	}
}
