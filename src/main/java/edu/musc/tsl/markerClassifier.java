package edu.musc.tsl;

import java.awt.Color;
import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.net.URLConnection;
import java.util.ArrayList;

import javax.imageio.ImageIO;

import org.apache.commons.collections15.Bag;
import org.apache.commons.collections15.bag.HashBag;

import ij.IJ;
import weka.classifiers.Classifier;
import weka.classifiers.bayes.NaiveBayes;
import weka.classifiers.functions.Logistic;
import weka.core.Instance;
import weka.core.Attribute;
import weka.core.DenseInstance;
import weka.core.Instances;

public class markerClassifier {

	private Classifier classifier;
	private Instances trainingDataset;
	private Instances testingDataset;
	private int nbFeatures;

	/** define the number of features to be used for training */
	public void defineNbFeatures(int nbF) {
		nbFeatures = nbF;
	}
	
	/** initialize training dataset */
	public void initializeTrainingDataset() {
		ArrayList<Attribute> atts = new ArrayList<Attribute>(nbFeatures);
        ArrayList<String> classVal = new ArrayList<String>();
        classVal.add("Positive");
        classVal.add("Negative");
        atts.add(new Attribute(new String("AvgIntensity")));
        atts.add(new Attribute(new String("StdIntensity")));
        atts.add(new Attribute(new String("Circularity")));
        atts.add(new Attribute(new String("Size")));
        atts.add(new Attribute("class",classVal));
        trainingDataset = new Instances("TrainingInstances",atts,0);
	}

	/** add element to training dataset */
	public void addTrainingDatasetElement(double avgI, double stdI, double circ, double size, double cl) {
        double[] instanceValue = new double[nbFeatures];
        instanceValue[0] = avgI;
        instanceValue[1] = stdI;
        instanceValue[2] = circ;
        instanceValue[3] = size;
        instanceValue[4] = cl;
        trainingDataset.add(new DenseInstance(1.0, instanceValue));
	}

	/** initialize testing dataset */
	public void initializeTestingDataset(){
		ArrayList<Attribute> atts = new ArrayList<Attribute>(nbFeatures);
		ArrayList<String> classVal = new ArrayList<String>();
		classVal.add("Positive");
		classVal.add("Negative");
		atts.add(new Attribute(new String("AvgIntensity")));
		atts.add(new Attribute(new String("StdIntensity")));
		atts.add(new Attribute(new String("Circularity")));
        atts.add(new Attribute(new String("Size")));
		atts.add(new Attribute("class",classVal));
		testingDataset = new Instances("TestingInstances",atts,0);
	}
	
	/** add element to testing dataset */
	public void addTestingDatasetElement(double avgI, double stdI, double circ, double size) {
        double[] instanceValue = new double[nbFeatures];
        instanceValue[0] = avgI;
        instanceValue[1] = stdI;
        instanceValue[2] = circ;
        instanceValue[3] = size;
        testingDataset.add(new DenseInstance(1.0, instanceValue));
	}

	/** train classifier */
	public void train() throws Exception {
		Logistic log = new Logistic();
		//IJ.showMessage("Default ridge: " + log.getRidge()); 1e-08
		log.setRidge(0.001);
		classifier = log;
		// our class is the last attribute
		trainingDataset.setClassIndex(trainingDataset.numAttributes() - 1);
		classifier.buildClassifier(trainingDataset);
	}

	public void showTrainingDataset(){
		IJ.log("Training dataset\n" + trainingDataset);
	}

	/** process classifier */
	public boolean[] test() throws Exception {
		boolean[] output = new boolean[testingDataset.size()];
		for(int i=0;i<testingDataset.size();i++){
			double[] distribution = classifier.distributionForInstance(testingDataset.get(i));
			if(distribution[0] > distribution[1]){
				output[i] = true; 
			}
			else{
				output[i] = false;
			}
		}
		return output;
	}
	
	/** process classifier */
	public void test(Instance inst) throws Exception {
		double[] distribution = classifier.distributionForInstance(inst);
		IJ.log("Result for instance: " + (distribution[0] > distribution[1] ? "Positive" : "Negative"));
	}
	
}
