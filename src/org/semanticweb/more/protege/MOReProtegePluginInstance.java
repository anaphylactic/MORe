package org.semanticweb.more.protege;

import org.protege.editor.owl.model.inference.AbstractProtegeOWLReasonerInfo;
import org.semanticweb.more.reasoner.MOReReasonerConfiguration;
import org.semanticweb.more.reasoner.MOReReasonerFactory;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.ReasonerProgressMonitor;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;


/**
 * MORe HermiT
 * Entry point for Protege reasoner plugin (i.e. Protege Factory). 
 * Extends AbstractProtegeOWLReasonerInfo and Implements ProtegePluginInstance
 * 
 * 
 * 
 * @author Ernesto Jimenez-Ruiz
 * @author Ana Armas
 *
 */
public class MOReProtegePluginInstance extends AbstractProtegeOWLReasonerInfo {
	
	protected final OWLReasonerFactory factory = new MOReReasonerFactory();

	@Override
	public BufferingMode getRecommendedBuffering() {
		return BufferingMode.BUFFERING;
	}

	@Override
	public OWLReasonerFactory getReasonerFactory() {
		return factory;
	}

	@Override
	public void initialise() throws Exception { }

	@Override
	public void dispose() throws Exception { }

	@Override
    public OWLReasonerConfiguration getConfiguration(ReasonerProgressMonitor monitor) {
    	return new MOReReasonerConfiguration(false);
    }
	
}
