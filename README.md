# MORe
Modular OWL 2 Reasoner for Ontology Classification

To build the project, modify the pom.xml file by replacing the line 
```xml
<systemPath>${basedir}/lib/RDFox/JRDFox.jar</systemPath>
```
with
```xml
<systemPath>${basedir}/lib/RDFox/Mac/JRDFox.jar</systemPath>
```
or
```xml
<systemPath>${basedir}/lib/RDFox/Linux/JRDFox.jar</systemPath>
```
or 
```xml
<systemPath>${basedir}/lib/RDFox/Windows/JRDFox.jar</systemPath>
```
according to your operating system, and then run maven.

Given an instance ```o``` of the ```OWLOntology``` class from  the [OWLAPI](http://owlapi.sourceforge.net/),  the simplest way to create an instance of the reasoner is the following:
```java
	MOReReasonerFactory factory = new MOReReasonerFactory();
	MoreReasoner more = factory.createReasoner(o);
```
To classify your ontology, simply call
```java
	more.classifyClasses();
```
You can retrieve all the superclasses of any ```OWLClass c``` in the input ontology by calling
```java
	more.getAllSuperClasses(c);
```
and also all unsatisfiable classes in the ontology with
```java
	more.getAllUnsatisfiableClasses();
```
The default configuration of MORe splits the classification workload between the reasoners ELK and HermiT, but you can configure MORe to split the workload between ELK, RDFox and HermiT
as follows
```java
	boolean useRDFox = true;
	MOReReasonerConfiguration config = new MOReReasonerConfiguration(useRDFox);
	MOReReasonerFactory factory = new MOReReasonerFactory();
	MOReReasoner more = factory.createReasoner(o, config);
```
It is also possible to make MORe combine ELK (and maybe RDFox) with any other OWL 2 reasoner that implements the ```OWLReasoner``` interface from the OWLAPI and can be created with an ```OWLReasonerFactory```. For this, it suffices to provide an instance ```owl2RsnrFactory``` of the corresponding ```OWLReasonerFactory``` and an instance  ```owl2RsnrConfig``` of the corresponding ```OWL2ReasonerConfiguration```  as arguments when creating ```more``` as follows:
```java
	MOReReasoner more = factory.createReasoner(o, config, owl2RsnrFactory, owl2RsnrConfig);
```