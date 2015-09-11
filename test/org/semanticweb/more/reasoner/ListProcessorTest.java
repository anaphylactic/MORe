package org.semanticweb.more.reasoner;

import static org.junit.Assert.*;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.more.reasoner.ListProcessor;
import org.semanticweb.more.util.Utility;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.PrefixManager;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;


public class ListProcessorTest{

	public static OWLClass a;
	public static OWLClass b;
	public static OWLClass c;
	public static OWLClass d;
	public static OWLClass e;
	public static OWLClass f;
	public static OWLObjectProperty r;
	
	
	@BeforeClass
	public static void setUp(){
		OWLDataFactory factory = new OWLDataFactoryImpl();
		PrefixManager prefManager = new DefaultPrefixManager();
		a = factory.getOWLClass("A",prefManager);
		b = factory.getOWLClass("B",prefManager);
		c = factory.getOWLClass("C",prefManager);
		d = factory.getOWLClass("D",prefManager);
		e = factory.getOWLClass("E",prefManager);
		f = factory.getOWLClass("F",prefManager);
		r = factory.getOWLObjectProperty("R", prefManager);

	}
	
	@Test
	public void testGetMinimalCombination() {
		List<List<Set<OWLEntity>>> mainList = new LinkedList<List<Set<OWLEntity>>>();
		List<Set<OWLEntity>> auxList = new LinkedList<Set<OWLEntity>>();
		Set<OWLEntity> auxSet = new HashSet<OWLEntity>();

		auxSet.add(a);
		auxSet.add(b);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		
		auxSet.add(r);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		mainList.add(auxList);
		auxList = new LinkedList<Set<OWLEntity>>();
		
		
		auxSet.add(a);
		auxSet.add(d);
		auxSet.add(e);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();

		auxSet.add(c);
		auxSet.add(d);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();

		auxSet.add(b);
		auxSet.add(r);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		mainList.add(auxList);
		auxList = new LinkedList<Set<OWLEntity>>();

		
		auxSet.add(e);
		auxSet.add(f);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		
		auxSet.add(d);
		auxSet.add(c);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		mainList.add(auxList);
		auxList = new LinkedList<Set<OWLEntity>>();
		
		
		Set<OWLEntity> expectedResult = new HashSet<OWLEntity>();
		expectedResult.add(a);
		expectedResult.add(b);
		expectedResult.add(d);
		expectedResult.add(e);
		expectedResult.add(f);

		ListProcessor tester = new ListProcessor();
		assertTrue(Utility.compareCollections(expectedResult, tester.getMinimalCombination(mainList, 10)));
	}

	@Test
	public void testAddsFewest() {
		List<Set<OWLEntity>> list = new LinkedList<Set<OWLEntity>>();
		Set<OWLEntity> auxSet = new HashSet<OWLEntity>();

		auxSet.add(e);
		auxSet.add(f);
		list.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		
		auxSet.add(d);
		auxSet.add(f);
		list.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		
		auxSet.add(e);
		auxSet.add(r);
		list.add(auxSet);
		auxSet = new HashSet<OWLEntity>();

		auxSet.add(a);
		auxSet.add(b);
		auxSet.add(d);

		
		Set<OWLEntity> expectedResult = new HashSet<OWLEntity>();
		expectedResult.add(d);
		expectedResult.add(f);
		
		ListProcessor tester = new ListProcessor();
		assertTrue(Utility.compareCollections(expectedResult, tester.addsFewest(list, auxSet, 10)));
	}

	@Test
	public void testGetBestCombination() { //not taking into account preferring to keep properties here...
		List<Set<OWLEntity>> list1 = new LinkedList<Set<OWLEntity>>();
		List<Set<OWLEntity>> list2 = new LinkedList<Set<OWLEntity>>();
		Set<OWLEntity> auxSet = new HashSet<OWLEntity>();

		auxSet.add(a);
		auxSet.add(b);
		list1.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(c);
		auxSet.add(e);
		list1.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(e);
		auxSet.add(f);
		list1.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		
		auxSet.add(a);
		auxSet.add(c);
		auxSet.add(d);
		list2.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		auxSet.add(f);
		list2.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		list2.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
				
		Set<OWLEntity> expectedResult = new HashSet<OWLEntity>();
		expectedResult.add(a);
		expectedResult.add(b);
		
		ListProcessor tester = new ListProcessor();
		assertTrue(Utility.compareCollections(expectedResult, tester.getBestCombination(list1, list2, 10)));
	}
	
	@Test
	public void testGetAllCombinations() {
		List<List<Set<OWLEntity>>> mainList = new LinkedList<List<Set<OWLEntity>>>();
		List<Set<OWLEntity>> auxList = new LinkedList<Set<OWLEntity>>();
		Set<OWLEntity> auxSet = new HashSet<OWLEntity>();

		auxSet.add(a);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		mainList.add(auxList);
		auxList = new LinkedList<Set<OWLEntity>>();
		
		auxSet.add(c);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(d);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(e);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		mainList.add(auxList);
		auxList = new LinkedList<Set<OWLEntity>>();

		auxSet.add(f);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(r);
		auxList.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		mainList.add(auxList);
		auxList = new LinkedList<Set<OWLEntity>>();

		
		List<Set<OWLEntity>> expectedResult = new LinkedList<Set<OWLEntity>>();
		auxSet.add(a);
		auxSet.add(c);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(c);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(d);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(d);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(e);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(e);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(d);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(d);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(e);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(e);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();

		ListProcessor tester = new ListProcessor();
		assertTrue(Utility.compareCollections(expectedResult, tester.getAllCombinations(mainList, true)));
		
		expectedResult = new LinkedList<Set<OWLEntity>>();
		auxSet.add(c);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(c);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(d);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(d);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(e);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(e);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(f);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(r);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(c);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(d);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(a);
		auxSet.add(e);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(c);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(d);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		auxSet.add(b);
		auxSet.add(e);
		expectedResult.add(auxSet);
		auxSet = new HashSet<OWLEntity>();
		
		assertTrue(Utility.compareCollections(expectedResult, tester.getAllCombinations(mainList, false)));
	}
	

}
