package org.semanticweb.more.visitors;

import org.semanticweb.owlapi.model.OWLAxiomVisitor;

public interface OWLFragmentVisitor extends OWLAxiomVisitor{

	boolean isInFragment();
}
