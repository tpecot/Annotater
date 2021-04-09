/*
 * This program is free software; you can redistribute it and/or modify it under the terms of the GNU Affero General Public License version 3 as published by the Free Software Foundation:
http://www.gnu.org/licenses/agpl-3.0.txt
 */

package edu.musc.tsl;

import net.imglib2.type.numeric.RealType;

import org.apache.commons.lang3.ObjectUtils.Null;
import org.scijava.command.Command;
import org.scijava.plugin.Plugin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.lang.Math;
import java.io.*;

import ij.*;
import ij.Prefs.*;
import ij.gui.*;
import ij.process.*;
import ij.measure.*;
import ij.io.*;
import ij.util.Tools;
import ij.IJ.*;
import ij.plugin.frame.RoiManager;
import ij.plugin.filter.ParticleAnalyzer;
import ij.ImagePlus;
import ij.ImageStack;
import ij.LookUpTable;
import ij.WindowManager;
import ij.plugin.CompositeConverter;
import ij.plugin.Duplicator;
import ij.plugin.HyperStackConverter;
import ij.plugin.filter.Analyzer;
import ij.plugin.filter.Binary;
import ij.plugin.filter.LutApplier;
import ij.plugin.filter.GaussianBlur;
import ij.macro.Interpreter;
import ij.Macro;
import ij.plugin.frame.Editor;
import ij.text.TextWindow;

import fiji.util.gui.GenericDialogPlus;
import fiji.util.gui.OverlayedImageCanvas;

import java.lang.reflect.*;

import java.awt.*;
import java.awt.image.*;
import java.awt.event.*;

import java.util.*;
import java.util.concurrent.*;

import javax.swing.*;
import javax.swing.event.*;

import weka.classifiers.*;
import weka.core.*;

@Plugin(type = Command.class, menuPath = "Plugins>Annotater")
public class Annotater<T extends RealType<T>> implements Command {

	String imageFilePath;
	/** maximum number of classes (labels) allowed on the GUI*/
	private static final int MAX_NUM_CLASSES = 5;
	private static final int MAX_NUM_MARKERS = 7;
	/** number of features to be used for ML */
	private final int nbFeatures = 5;
	/** plugin opening **/
	private boolean on = false;
	/** current mode: 0 -> nuclei annotation; 2: -> marker annotation **/
	private byte currentMode = 0;
	/** class currently added **/
	private byte currentClass = 0;
	/** array of lists of Rois for each class */
	private List<Point[]> [] objectsInEachClass = new ArrayList[MAX_NUM_CLASSES];
	/** overlay to display the objects for each class */
	private Overlay overlay;
	/** overlay to display the markers for each class */
	private Overlay markersOverlay;
	/** overlay to display the areas */
	private Overlay areaOverlay;
	/** image to display on the GUI, it includes the painted rois */
	private ImagePlus displayImage;
	/** channel displayed */
	private byte currentDisplayedChannel = -1;
	/** GUI window */
	private CustomWindow win;
	/** flag for rois **/
	private short[][][] roiFlag;
	/** flag for display mode **/
	private byte displayFlag = 0;
	/** mouse panning */
	private boolean mousePanning = false;
	/** flag object displaying **/
	private boolean objectDisplayFlag = true;
	/** flag area displaying **/
	private boolean areaDisplayFlag = true;
	/** flag for ML labelling **/
	private boolean positiveLabelFlag = true;
	/** deal with double click **/
	private double previous_click_time = 0;
	
	/** marker currently annotated **/
	private int currentObjectAssociatedMarker = -1;
	/** pattern for channel currently annotated **/
	private int currentPattern = -1;
	/** array of lists of positively marked Rois for each marker */
	private List<Short> [][] positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
	/** array of lists of positively labelled Rois for each marker */
	private List<Short> [] positivelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
	/** array of lists of negatively labelled Rois for each marker */
	private List<Short> [] negativelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
	/** array of lists of features for ML */
	private List<double[]> [] featuresForEachMarker = new ArrayList[MAX_NUM_MARKERS];
	
	/** marker currently annotated **/
	private byte currentArea = 0;
	/** array of lists of Rois for each class */
	private List<Point[]> [] areasInEachClass = new ArrayList[MAX_NUM_CLASSES];
	/** flag for areas **/
	private short[][][] areaFlag;

	/** nuclei annotation mode button */
	private JRadioButton objectsAnnotationButton;
	/** marker annotation mode button */
	private JRadioButton markerAnnotationButton;

	/** new object button */
	private JRadioButton newObjectButton;
	/** remove object button */
	private JRadioButton removeObjectButton;
	/** merge objects button */
	private JRadioButton mergeObjectsButton;
	/** split objects button */
	private JRadioButton splitObjectsButton;
	/** swap class button */
	private JRadioButton swapObjectClassButton;

	/** new object button */
	private JRadioButton newAreaButton;
	/** remove object button */
	private JRadioButton removeAreaButton;
	/** swap class button */
	private JRadioButton swapAreaClassButton;

	/** create a new ROI listener to add ROI for each object **/
	RoiListener roiListener;
	/** create a new KeyAction to allow the user to interact with the keyboard for navigation**/
	KeyActions keyListener;

	/** transparent colors to make nuclei disappear */
	public Color transparentColor = new Color(255, 255, 255, 0);
	/** available colors for available classes*/
	private final Color[] colors = new Color[]{Color.red, Color.green, Color.blue, Color.yellow, Color.magenta, Color.cyan, Color.orange, Color.pink, Color.black, Color.gray, Color.white};
	/** available color model channels for areas*/
	private final IndexColorModel[] areaColorModels = new IndexColorModel[10];

	/** color indices for classes */
	private byte[] classColors = new byte[]{0, -1, -1, -1, -1};
	/** color indices for object associated markers */
	private byte[][] objectAssociatedMarkersColors = new byte[][]{{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7}};
	/** color indices for object associated markers with ML */
	private byte[][] objectAssociatedMarkersMLColors = new byte[][]{{1, 2, 4},{1, 2, 4},{1, 2, 4},{1, 2, 4},{1, 2, 4},{1, 2, 4},{1, 2, 4},{1, 2, 4},{1, 2, 4},{1, 2, 4}};
	/** cell compartment index for markers: 0 -> nuclear, 1 -> membranar, 2 -> cytoplasmic */
	private byte[] markerCellcompartment = new byte[]{0,0,0,0,0,0,0};
	/** method used to identify markers: 0 -> manual, 1 -> thresholding, 2 -> ML */
	private byte[] methodToIdentifyObjectAssociatedMarkers = new byte[]{0,0,0,0,0,0,0};
	/** channel to be thresholded */
	private byte[] channelsForObjectAssociatedMarkers = new byte[]{-1,-1,-1,-1,-1,-1,-1};
	/** thresholds for markers */
	private int[][] thresholdsForObjectAssociatedMarkers = new int[][]{{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1}};
	/** current number of classes */
	private byte numOfClasses = 1;
	/** current number of markers */
	private byte numOfObjectAssociatedMarkers = 0;
	/** current number of channels */
	private byte numOfChannels = 1;
	/** chosen channel for marker thresholding*/
	private byte chosenChannelForObjectAssociatedMarker = 0;
	/** combination of markers */
	int nbCombinations = 0;
	String[] combinationNames = new String[64];
	short[][] markerCombinations = new short[64][7];

	/** color indices for thresholded markers */
	private byte[] areaColors = new byte[]{0, -1, -1, -1, -1};
	/** current number of markers */
	private byte numOfAreas = 1;

	/** flags to know if cell compartments need to be computed */
	boolean nuclearComponentFlag = false;
	boolean innerNuclearComponentFlag = false;
	boolean membranarComponentFlag = false;
	boolean cytoplasmicComponentFlag = false;
	/** tables for different cell compartments */
	private int[][][] nuclearComponent;
	private int[][][] innerNuclearComponent;
	private int[][][] membranarComponent;
	private int[][][] cytoplasmicComponent;
	/** flag to know if result table for ML has already been computed */
	boolean rt_nuclearML_flag = false;
	/** result table for ML */
	private ResultsTable rt_nuclearML;
	
	
	/** add class */
	private JButton addClassButton;
	/** radio buttons for selecting classes */
	private JRadioButton class1Button;
	private JRadioButton class2Button;
	private JRadioButton class3Button;
	private JRadioButton class4Button;
	private JRadioButton class5Button;
	/** buttons for selecting color associated with classes */
	private JButton class1ColorButton;
	private JButton class2ColorButton;
	private JButton class3ColorButton;
	private JButton class4ColorButton;
	private JButton class5ColorButton;
	/** buttons for deleting classes */
	private JButton class1RemoveButton;
	private JButton class2RemoveButton;
	private JButton class3RemoveButton;
	private JButton class4RemoveButton;
	private JButton class5RemoveButton;
	/** button to batch analyze each independent class */
	private JButton batchClassesMeasurementsButton;

	/** add area */
	private JButton addAreaButton;
	/** radio buttons for selecting classes */
	private JRadioButton area1Button;
	private JRadioButton area2Button;
	private JRadioButton area3Button;
	private JRadioButton area4Button;
	private JRadioButton area5Button;
	/** buttons for selecting color associated with areas */
	private JButton area1ColorButton;
	private JButton area2ColorButton;
	private JButton area3ColorButton;
	private JButton area4ColorButton;
	private JButton area5ColorButton;
	/** buttons for deleting areas */
	private JButton area1RemoveButton;
	private JButton area2RemoveButton;
	private JButton area3RemoveButton;
	private JButton area4RemoveButton;
	private JButton area5RemoveButton;

	/** button to analyze each independent class */
	private JButton analyzeClassesButton;
	/** button to visualize image with overlays for figure/presentation */
	private JButton classSnapshotButton;


	/** buttons to visualize each independent channel or all channels */
	private JRadioButton visualizeChannel1onlyButton1;
	private JRadioButton visualizeChannel2onlyButton1;
	private JRadioButton visualizeChannel3onlyButton1;
	private JRadioButton visualizeChannel4onlyButton1;
	private JRadioButton visualizeChannel5onlyButton1;
	private JRadioButton visualizeChannel6onlyButton1;
	private JRadioButton visualizeChannel7onlyButton1;
	private JRadioButton visualizeChannel1Button1;
	private JRadioButton visualizeChannel2Button1;
	private JRadioButton visualizeChannel3Button1;
	private JRadioButton visualizeChannel4Button1;
	private JRadioButton visualizeChannel5Button1;
	private JRadioButton visualizeChannel6Button1;
	private JRadioButton visualizeChannel7Button1;
	private JRadioButton visualizeAllChannelsButton1;
	private JRadioButton visualizeChannel1onlyButton2;
	private JRadioButton visualizeChannel2onlyButton2;
	private JRadioButton visualizeChannel3onlyButton2;
	private JRadioButton visualizeChannel4onlyButton2;
	private JRadioButton visualizeChannel5onlyButton2;
	private JRadioButton visualizeChannel6onlyButton2;
	private JRadioButton visualizeChannel7onlyButton2;
	private JRadioButton visualizeChannel1Button2;
	private JRadioButton visualizeChannel2Button2;
	private JRadioButton visualizeChannel3Button2;
	private JRadioButton visualizeChannel4Button2;
	private JRadioButton visualizeChannel5Button2;
	private JRadioButton visualizeChannel6Button2;
	private JRadioButton visualizeChannel7Button2;
	private JRadioButton visualizeAllChannelsButton2;

	/** visualize objects and areas */
	private JRadioButton visualizeObjectsButton1;
	private JRadioButton visualizeAreasButton1;
	private JRadioButton visualizeObjectsButton2;
	private JRadioButton visualizeAreasButton2;
	
	/** button to load a different couple of image and segmentation files */
	private JButton loadImageAndSegmentationButton;

	/** buttons to analyze each independent channel */
	/** add marker */
	private JButton addObjectAssociatedMarkerButton;

	/** radio buttons for object associated markers */
	private JRadioButton objectAssociatedMarker1Button;
	private JButton objectAssociatedMarker1ColorButton;
	private JButton objectAssociatedMarker1ColorMLButton;
	private JButton objectAssociatedMarker1RemoveButton;
	private JRadioButton objectAssociatedMarker1PositiveLabelButton;
	private JRadioButton objectAssociatedMarker1NegativeLabelButton;
	private JButton objectAssociatedMarker1TrainButton;
	private JButton objectAssociatedMarker1LoadButton;
	private JButton objectAssociatedMarker1SaveButton;
	private JRadioButton objectAssociatedMarker1Pattern1Button;
	private JRadioButton objectAssociatedMarker1Pattern2Button;
	private JRadioButton objectAssociatedMarker1Pattern3Button;
	private JRadioButton objectAssociatedMarker1Pattern4Button;
	private JRadioButton objectAssociatedMarker2Button;
	private JButton objectAssociatedMarker2ColorButton;
	private JButton objectAssociatedMarker2ColorMLButton;
	private JButton objectAssociatedMarker2RemoveButton;
	private JRadioButton objectAssociatedMarker2PositiveLabelButton;
	private JRadioButton objectAssociatedMarker2NegativeLabelButton;
	private JButton objectAssociatedMarker2TrainButton;
	private JButton objectAssociatedMarker2LoadButton;
	private JButton objectAssociatedMarker2SaveButton;
	private JRadioButton objectAssociatedMarker2Pattern1Button;
	private JRadioButton objectAssociatedMarker2Pattern2Button;
	private JRadioButton objectAssociatedMarker2Pattern3Button;
	private JRadioButton objectAssociatedMarker2Pattern4Button;
	private JRadioButton objectAssociatedMarker3Button;
	private JButton objectAssociatedMarker3ColorButton;
	private JButton objectAssociatedMarker3ColorMLButton;
	private JButton objectAssociatedMarker3RemoveButton;
	private JRadioButton objectAssociatedMarker3PositiveLabelButton;
	private JRadioButton objectAssociatedMarker3NegativeLabelButton;
	private JButton objectAssociatedMarker3TrainButton;
	private JButton objectAssociatedMarker3LoadButton;
	private JButton objectAssociatedMarker3SaveButton;
	private JRadioButton objectAssociatedMarker3Pattern1Button;
	private JRadioButton objectAssociatedMarker3Pattern2Button;
	private JRadioButton objectAssociatedMarker3Pattern3Button;
	private JRadioButton objectAssociatedMarker3Pattern4Button;
	private JRadioButton objectAssociatedMarker4Button;
	private JButton objectAssociatedMarker4ColorButton;
	private JButton objectAssociatedMarker4ColorMLButton;
	private JButton objectAssociatedMarker4RemoveButton;
	private JRadioButton objectAssociatedMarker4PositiveLabelButton;
	private JRadioButton objectAssociatedMarker4NegativeLabelButton;
	private JButton objectAssociatedMarker4TrainButton;
	private JButton objectAssociatedMarker4LoadButton;
	private JButton objectAssociatedMarker4SaveButton;
	private JRadioButton objectAssociatedMarker4Pattern1Button;
	private JRadioButton objectAssociatedMarker4Pattern2Button;
	private JRadioButton objectAssociatedMarker4Pattern3Button;
	private JRadioButton objectAssociatedMarker4Pattern4Button;
	private JRadioButton objectAssociatedMarker5Button;
	private JButton objectAssociatedMarker5ColorButton;
	private JButton objectAssociatedMarker5ColorMLButton;
	private JButton objectAssociatedMarker5RemoveButton;
	private JRadioButton objectAssociatedMarker5PositiveLabelButton;
	private JRadioButton objectAssociatedMarker5NegativeLabelButton;
	private JButton objectAssociatedMarker5TrainButton;
	private JButton objectAssociatedMarker5LoadButton;
	private JButton objectAssociatedMarker5SaveButton;
	private JRadioButton objectAssociatedMarker5Pattern1Button;
	private JRadioButton objectAssociatedMarker5Pattern2Button;
	private JRadioButton objectAssociatedMarker5Pattern3Button;
	private JRadioButton objectAssociatedMarker5Pattern4Button;
	private JRadioButton objectAssociatedMarker6Button;
	private JButton objectAssociatedMarker6ColorButton;
	private JButton objectAssociatedMarker6ColorMLButton;
	private JButton objectAssociatedMarker6RemoveButton;
	private JRadioButton objectAssociatedMarker6PositiveLabelButton;
	private JRadioButton objectAssociatedMarker6NegativeLabelButton;
	private JButton objectAssociatedMarker6TrainButton;
	private JButton objectAssociatedMarker6LoadButton;
	private JButton objectAssociatedMarker6SaveButton;
	private JRadioButton objectAssociatedMarker6Pattern1Button;
	private JRadioButton objectAssociatedMarker6Pattern2Button;
	private JRadioButton objectAssociatedMarker6Pattern3Button;
	private JRadioButton objectAssociatedMarker6Pattern4Button;
	private JRadioButton objectAssociatedMarker7Button;
	private JButton objectAssociatedMarker7ColorMLButton;
	private JButton objectAssociatedMarker7ColorButton;
	private JButton objectAssociatedMarker7RemoveButton;
	private JRadioButton objectAssociatedMarker7PositiveLabelButton;
	private JRadioButton objectAssociatedMarker7NegativeLabelButton;
	private JButton objectAssociatedMarker7TrainButton;
	private JButton objectAssociatedMarker7LoadButton;
	private JButton objectAssociatedMarker7SaveButton;
	private JRadioButton objectAssociatedMarker7Pattern1Button;
	private JRadioButton objectAssociatedMarker7Pattern2Button;
	private JRadioButton objectAssociatedMarker7Pattern3Button;
	private JRadioButton objectAssociatedMarker7Pattern4Button;

	/** buttons to analyze object associated markers */
	private JButton analyzeMarkersButton;
	/** button to batch analyze nuclei markers  */
	private JButton batchMarkersButton;
	/** button to visualize image with overlays for figure/presentation */
	private JButton markerSnapshotButton;

	/** buttons to load and save segmentations */
	private JButton loadSegmentationButton;
	private JButton saveSegmentationButton;
	private JButton loadObjectAssociatedMarkerButton;
	private JButton saveObjectAssociatedMarkerButton;
	private JButton loadAreaButton;
	private JButton saveAreaButton;

	/** executor service to launch threads for the plugin methods and events */
	private final ExecutorService exec = Executors.newFixedThreadPool(1);

	/** variables needed to merge objects */
	private short firstObjectToMerge_class,firstObjectToMerge_classId,firstObjectToMerge_overlayId;

	/** color buttons for classes */
	private JRadioButton redCheck;
	private JRadioButton greenCheck;
	private JRadioButton blueCheck;
	private JRadioButton yellowCheck;
	private JRadioButton magentaCheck;
	private JRadioButton cyanCheck;
	private JRadioButton orangeCheck;
	private JRadioButton pinkCheck;
	private JRadioButton blackCheck;
	private JRadioButton grayCheck;
	private JRadioButton whiteCheck;

	/** color buttons for marker patterns */
	private JRadioButton redCheck1;
	private JRadioButton greenCheck1;
	private JRadioButton blueCheck1;
	private JRadioButton yellowCheck1;
	private JRadioButton magentaCheck1;
	private JRadioButton cyanCheck1;
	private JRadioButton orangeCheck1;
	private JRadioButton pinkCheck1;
	private JRadioButton blackCheck1;
	private JRadioButton grayCheck1;
	private JRadioButton whiteCheck1;
	private JRadioButton redCheck2;
	private JRadioButton greenCheck2;
	private JRadioButton blueCheck2;
	private JRadioButton yellowCheck2;
	private JRadioButton magentaCheck2;
	private JRadioButton cyanCheck2;
	private JRadioButton orangeCheck2;
	private JRadioButton pinkCheck2;
	private JRadioButton blackCheck2;
	private JRadioButton grayCheck2;
	private JRadioButton whiteCheck2;
	private JRadioButton redCheck3;
	private JRadioButton greenCheck3;
	private JRadioButton blueCheck3;
	private JRadioButton yellowCheck3;
	private JRadioButton magentaCheck3;
	private JRadioButton cyanCheck3;
	private JRadioButton orangeCheck3;
	private JRadioButton pinkCheck3;
	private JRadioButton blackCheck3;
	private JRadioButton grayCheck3;
	private JRadioButton whiteCheck3;
	private JRadioButton redCheck4;
	private JRadioButton greenCheck4;
	private JRadioButton blueCheck4;
	private JRadioButton yellowCheck4;
	private JRadioButton magentaCheck4;
	private JRadioButton cyanCheck4;
	private JRadioButton orangeCheck4;
	private JRadioButton pinkCheck4;
	private JRadioButton blackCheck4;
	private JRadioButton grayCheck4;
	private JRadioButton whiteCheck4;

	/** slider bars for object associated marker thresholding */
	private JSlider intensityThresholdingForObjectAssociatedMarkerScrollBar;
	private JTextArea intensityThresholdingForObjectAssociatedMarkerTextArea;
	private JButton setIntensityThresholdForObjectAssociatedMarkerButton;
	private JSlider areaThresholdingScrollBar;
	private JTextArea areaThresholdingTextArea;
	private JButton setAreaThresholdButton;
	/** ok and cancel buttons for thresholding */
	private JButton okMarkerForObjectAssociatedMarkersButton;
	private JButton cancelMarkerForObjectAssociatedMarkersButton;
	/** variable used for marker thresholds */
	short[][] intensityThresholdsForObjectAssociatedMarkers;
	/** folder for batch processing */
	private String imageFolder = new String();
	private String segmentationFolder = new String();
	private String objectAssociatedMarkerFolder = new String();
	private String areaFolder = new String();
	private String measurementsFolder = new String();
	private String outputImageFolder = new String();
	private String imageFile = new String();
	private String segmentationFile = new String();
	

	/**
	 * Basic constructor
	 */
	public Annotater() 
	{
		objectsAnnotationButton = new JRadioButton("Object annotation");
		scale(objectsAnnotationButton);
		markerAnnotationButton = new JRadioButton("Marker annotation");
		scale(markerAnnotationButton);

		newObjectButton = new JRadioButton("Add object");
		scale(newObjectButton);
		newObjectButton.setToolTipText("Each ROI creates a new object");

		removeObjectButton = new JRadioButton("Remove object");
		scale(removeObjectButton);
		removeObjectButton.setToolTipText("Remove object");		

		mergeObjectsButton = new JRadioButton("Merge objects");
		scale(mergeObjectsButton);
		mergeObjectsButton.setToolTipText("Consecutively clicked objects are merged");

		splitObjectsButton = new JRadioButton("Split object");
		scale(splitObjectsButton);
		splitObjectsButton.setToolTipText("Draw ROI inside an object to split it into two");

		swapObjectClassButton = new JRadioButton("Swap class");
		scale(swapObjectClassButton);
		swapObjectClassButton.setToolTipText("Swap object class");

		addClassButton = new JButton("Add new class");
		scale(addClassButton);
		class1Button = new JRadioButton("Class 1");
		scale(class1Button);
		class2Button = new JRadioButton("Class 2");
		scale(class2Button);
		class3Button = new JRadioButton("Class 3");
		scale(class3Button);
		class4Button = new JRadioButton("Class 4");
		scale(class4Button);
		class5Button = new JRadioButton("Class 5");
		scale(class5Button);

		class1ColorButton = new JButton("Color");
		scale(class1ColorButton);
		class2ColorButton = new JButton("Color");
		scale(class2ColorButton);
		class3ColorButton = new JButton("Color");
		scale(class3ColorButton);
		class4ColorButton = new JButton("Color");
		scale(class4ColorButton);
		class5ColorButton = new JButton("Color");
		scale(class5ColorButton);

		class1RemoveButton = new JButton("Remove");
		scale(class1RemoveButton);
		class2RemoveButton = new JButton("Remove");
		scale(class2RemoveButton);
		class3RemoveButton = new JButton("Remove");
		scale(class3RemoveButton);
		class4RemoveButton = new JButton("Remove");
		scale(class4RemoveButton);
		class5RemoveButton = new JButton("Remove");
		scale(class5RemoveButton);

		newAreaButton = new JRadioButton("Add area");
		scale(newAreaButton);
		removeAreaButton = new JRadioButton("Remove area");
		scale(removeAreaButton);
		swapAreaClassButton = new JRadioButton("Swap class");
		scale(swapAreaClassButton);

		addAreaButton = new JButton("Add new class");
		scale(addAreaButton);
		area1Button = new JRadioButton("Class 1");
		scale(area1Button);
		area2Button = new JRadioButton("Class 2");
		scale(area2Button);
		area3Button = new JRadioButton("Class 3");
		scale(area3Button);
		area4Button = new JRadioButton("Class 4");
		scale(area4Button);
		area5Button = new JRadioButton("Class 5");
		scale(area5Button);

		area1ColorButton = new JButton("Color");
		scale(area1ColorButton);
		area2ColorButton = new JButton("Color");
		scale(area2ColorButton);
		area3ColorButton = new JButton("Color");
		scale(area3ColorButton);
		area4ColorButton = new JButton("Color");
		scale(area4ColorButton);
		area5ColorButton = new JButton("Color");
		scale(area5ColorButton);

		area1RemoveButton = new JButton("Remove");
		scale(area1RemoveButton);
		area2RemoveButton = new JButton("Remove");
		scale(area2RemoveButton);
		area3RemoveButton = new JButton("Remove");
		scale(area3RemoveButton);
		area4RemoveButton = new JButton("Remove");
		scale(area4RemoveButton);
		area5RemoveButton = new JButton("Remove");
		scale(area5RemoveButton);

		loadSegmentationButton = new JButton("Load");
		scale(loadSegmentationButton);
		saveSegmentationButton = new JButton("Save");
		scale(saveSegmentationButton);
		loadAreaButton = new JButton("Load");
		scale(loadAreaButton);
		saveAreaButton = new JButton("Save");
		scale(saveAreaButton);
		analyzeClassesButton = new JButton("Measurements");
		scale(analyzeClassesButton);
		classSnapshotButton = new JButton("Snapshot");
		scale(classSnapshotButton);
		batchClassesMeasurementsButton = new JButton("Batch");
		scale(batchClassesMeasurementsButton);
		overlay = new Overlay();
		areaOverlay = new Overlay();

		visualizeChannel1onlyButton1 = new JRadioButton("Channel1 only");
		scale(visualizeChannel1onlyButton1);
		visualizeChannel2onlyButton1 = new JRadioButton("Channel2 only");
		scale(visualizeChannel2onlyButton1);
		visualizeChannel3onlyButton1 = new JRadioButton("Channel3 only");
		scale(visualizeChannel3onlyButton1);
		visualizeChannel4onlyButton1 = new JRadioButton("Channel4 only");
		scale(visualizeChannel4onlyButton1);
		visualizeChannel5onlyButton1 = new JRadioButton("Channel5 only");
		scale(visualizeChannel5onlyButton1);
		visualizeChannel6onlyButton1 = new JRadioButton("Channel6 only");
		scale(visualizeChannel6onlyButton1);
		visualizeChannel7onlyButton1 = new JRadioButton("Channel7 only");
		scale(visualizeChannel7onlyButton1);
		visualizeChannel1Button1 = new JRadioButton("Channel1");
		scale(visualizeChannel1Button1);
		visualizeChannel2Button1 = new JRadioButton("Channel2");
		scale(visualizeChannel2Button1);
		visualizeChannel3Button1 = new JRadioButton("Channel3");
		scale(visualizeChannel3Button1);
		visualizeChannel4Button1 = new JRadioButton("Channel4");
		scale(visualizeChannel4Button1);
		visualizeChannel5Button1 = new JRadioButton("Channel5");
		scale(visualizeChannel5Button1);
		visualizeChannel6Button1 = new JRadioButton("Channel6");
		scale(visualizeChannel6Button1);
		visualizeChannel7Button1 = new JRadioButton("Channel7");
		scale(visualizeChannel7Button1);
		visualizeAllChannelsButton1 = new JRadioButton("All channels");
		scale(visualizeAllChannelsButton1);

		visualizeChannel1onlyButton2 = new JRadioButton("Channel1 only");
		scale(visualizeChannel1onlyButton2);
		visualizeChannel2onlyButton2 = new JRadioButton("Channel2 only");
		scale(visualizeChannel2onlyButton2);
		visualizeChannel3onlyButton2 = new JRadioButton("Channel3 only");
		scale(visualizeChannel3onlyButton2);
		visualizeChannel4onlyButton2 = new JRadioButton("Channel4 only");
		scale(visualizeChannel4onlyButton2);
		visualizeChannel5onlyButton2 = new JRadioButton("Channel5 only");
		scale(visualizeChannel5onlyButton2);
		visualizeChannel6onlyButton2 = new JRadioButton("Channel6 only");
		scale(visualizeChannel6onlyButton2);
		visualizeChannel7onlyButton2 = new JRadioButton("Channel7 only");
		scale(visualizeChannel7onlyButton2);
		visualizeChannel1Button2 = new JRadioButton("Channel1");
		scale(visualizeChannel1Button2);
		visualizeChannel2Button2 = new JRadioButton("Channel2");
		scale(visualizeChannel2Button2);
		visualizeChannel3Button2 = new JRadioButton("Channel3");
		scale(visualizeChannel3Button2);
		visualizeChannel4Button2 = new JRadioButton("Channel4");
		scale(visualizeChannel4Button2);
		visualizeChannel5Button2 = new JRadioButton("Channel5");
		scale(visualizeChannel5Button2);
		visualizeChannel6Button2 = new JRadioButton("Channel6");
		scale(visualizeChannel6Button2);
		visualizeChannel7Button2 = new JRadioButton("Channel7");
		scale(visualizeChannel7Button2);
		visualizeAllChannelsButton2 = new JRadioButton("All channels");
		scale(visualizeAllChannelsButton2);

		visualizeObjectsButton1 = new JRadioButton("Objects");
		scale(visualizeObjectsButton1);
		visualizeObjectsButton1.setSelected(true);
		visualizeAreasButton1 = new JRadioButton("Regions");
		scale(visualizeAreasButton1);
		visualizeAreasButton1.setSelected(true);
		visualizeObjectsButton2 = new JRadioButton("Objects");
		scale(visualizeObjectsButton2);
		visualizeAreasButton2 = new JRadioButton("Regions");
		scale(visualizeAreasButton2);
		
		loadImageAndSegmentationButton = new JButton("Load");
		scale(loadImageAndSegmentationButton);
		
		addObjectAssociatedMarkerButton = new JButton("Add new marker");
		scale(addObjectAssociatedMarkerButton);
		objectAssociatedMarker1Button = new JRadioButton("Marker1");
		scale(objectAssociatedMarker1Button);
		objectAssociatedMarker1ColorButton = new JButton("Color");
		scale(objectAssociatedMarker1ColorButton);
		objectAssociatedMarker1ColorMLButton = new JButton("Color");
		scale(objectAssociatedMarker1ColorMLButton);
		objectAssociatedMarker1RemoveButton = new JButton("Remove");
		scale(objectAssociatedMarker1RemoveButton);
		objectAssociatedMarker1PositiveLabelButton = new JRadioButton("M+");
		scale(objectAssociatedMarker1PositiveLabelButton);
		objectAssociatedMarker1NegativeLabelButton = new JRadioButton("M-");
		scale(objectAssociatedMarker1NegativeLabelButton);
		objectAssociatedMarker1TrainButton = new JButton("Train");
		scale(objectAssociatedMarker1TrainButton);
		objectAssociatedMarker1LoadButton = new JButton("Load");
		scale(objectAssociatedMarker1LoadButton);
		objectAssociatedMarker1SaveButton = new JButton("Save");
		scale(objectAssociatedMarker1SaveButton);
		objectAssociatedMarker1Pattern1Button = new JRadioButton("P1");
		scale(objectAssociatedMarker1Pattern1Button);
		objectAssociatedMarker1Pattern2Button = new JRadioButton("P2");
		scale(objectAssociatedMarker1Pattern2Button);
		objectAssociatedMarker1Pattern3Button = new JRadioButton("P3");
		scale(objectAssociatedMarker1Pattern3Button);
		objectAssociatedMarker1Pattern4Button = new JRadioButton("P4");
		scale(objectAssociatedMarker1Pattern4Button);
		objectAssociatedMarker2Button = new JRadioButton("Marker2");
		scale(objectAssociatedMarker2Button);
		objectAssociatedMarker2ColorButton = new JButton("Color");
		scale(objectAssociatedMarker2ColorButton);
		objectAssociatedMarker2ColorMLButton = new JButton("Color");
		scale(objectAssociatedMarker2ColorMLButton);
		objectAssociatedMarker2RemoveButton = new JButton("Remove");
		scale(objectAssociatedMarker2RemoveButton);
		objectAssociatedMarker2PositiveLabelButton = new JRadioButton("M+");
		scale(objectAssociatedMarker2PositiveLabelButton);
		objectAssociatedMarker2NegativeLabelButton = new JRadioButton("M-");
		scale(objectAssociatedMarker2NegativeLabelButton);
		objectAssociatedMarker2TrainButton = new JButton("Train");
		scale(objectAssociatedMarker2TrainButton);
		objectAssociatedMarker2LoadButton = new JButton("Load");
		scale(objectAssociatedMarker2LoadButton);
		objectAssociatedMarker2SaveButton = new JButton("Save");
		scale(objectAssociatedMarker2SaveButton);
		objectAssociatedMarker2Pattern1Button = new JRadioButton("P1");
		scale(objectAssociatedMarker2Pattern1Button);
		objectAssociatedMarker2Pattern2Button = new JRadioButton("P2");
		scale(objectAssociatedMarker2Pattern2Button);
		objectAssociatedMarker2Pattern3Button = new JRadioButton("P3");
		scale(objectAssociatedMarker2Pattern3Button);
		objectAssociatedMarker2Pattern4Button = new JRadioButton("P4");
		scale(objectAssociatedMarker2Pattern4Button);
		objectAssociatedMarker3Button = new JRadioButton("Marker3");
		scale(objectAssociatedMarker3Button);
		objectAssociatedMarker3ColorButton = new JButton("Color");
		scale(objectAssociatedMarker3ColorButton);
		objectAssociatedMarker3ColorMLButton = new JButton("Color");
		scale(objectAssociatedMarker3ColorMLButton);
		objectAssociatedMarker3RemoveButton = new JButton("Remove");
		scale(objectAssociatedMarker3RemoveButton);
		objectAssociatedMarker3PositiveLabelButton = new JRadioButton("M+");
		scale(objectAssociatedMarker3PositiveLabelButton);
		objectAssociatedMarker3NegativeLabelButton = new JRadioButton("M-");
		scale(objectAssociatedMarker3NegativeLabelButton);
		objectAssociatedMarker3TrainButton = new JButton("Train");
		scale(objectAssociatedMarker3TrainButton);
		objectAssociatedMarker3LoadButton = new JButton("Load");
		scale(objectAssociatedMarker3LoadButton);
		objectAssociatedMarker3SaveButton = new JButton("Save");
		scale(objectAssociatedMarker3SaveButton);
		objectAssociatedMarker3Pattern1Button = new JRadioButton("P1");
		scale(objectAssociatedMarker3Pattern1Button);
		objectAssociatedMarker3Pattern2Button = new JRadioButton("P2");
		scale(objectAssociatedMarker3Pattern2Button);
		objectAssociatedMarker3Pattern3Button = new JRadioButton("P3");
		scale(objectAssociatedMarker3Pattern3Button);
		objectAssociatedMarker3Pattern4Button = new JRadioButton("P4");
		scale(objectAssociatedMarker3Pattern4Button);
		objectAssociatedMarker4Button = new JRadioButton("Marker4");
		scale(objectAssociatedMarker4Button);
		objectAssociatedMarker4ColorButton = new JButton("Color");
		scale(objectAssociatedMarker4ColorButton);
		objectAssociatedMarker4ColorMLButton = new JButton("Color");
		scale(objectAssociatedMarker4ColorMLButton);
		objectAssociatedMarker4RemoveButton = new JButton("Remove");
		scale(objectAssociatedMarker4RemoveButton);
		objectAssociatedMarker4PositiveLabelButton = new JRadioButton("M+");
		scale(objectAssociatedMarker4PositiveLabelButton);
		objectAssociatedMarker4NegativeLabelButton = new JRadioButton("M-");
		scale(objectAssociatedMarker4NegativeLabelButton);
		objectAssociatedMarker4TrainButton = new JButton("Train");
		scale(objectAssociatedMarker4TrainButton);
		objectAssociatedMarker4LoadButton = new JButton("Load");
		scale(objectAssociatedMarker4LoadButton);
		objectAssociatedMarker4SaveButton = new JButton("Save");
		scale(objectAssociatedMarker4SaveButton);
		objectAssociatedMarker4Pattern1Button = new JRadioButton("P1");
		scale(objectAssociatedMarker4Pattern1Button);
		objectAssociatedMarker4Pattern2Button = new JRadioButton("P2");
		scale(objectAssociatedMarker4Pattern2Button);
		objectAssociatedMarker4Pattern3Button = new JRadioButton("P3");
		scale(objectAssociatedMarker4Pattern3Button);
		objectAssociatedMarker4Pattern4Button = new JRadioButton("P4");
		scale(objectAssociatedMarker4Pattern4Button);
		objectAssociatedMarker5Button = new JRadioButton("Marker5");
		scale(objectAssociatedMarker5Button);
		objectAssociatedMarker5ColorButton = new JButton("Color");
		scale(objectAssociatedMarker5ColorButton);
		objectAssociatedMarker5ColorMLButton = new JButton("Color");
		scale(objectAssociatedMarker5ColorMLButton);
		objectAssociatedMarker5RemoveButton = new JButton("Remove");
		scale(objectAssociatedMarker5RemoveButton);
		objectAssociatedMarker5PositiveLabelButton = new JRadioButton("M+");
		scale(objectAssociatedMarker5PositiveLabelButton);
		objectAssociatedMarker5NegativeLabelButton = new JRadioButton("M-");
		scale(objectAssociatedMarker5NegativeLabelButton);
		objectAssociatedMarker5TrainButton = new JButton("Train");
		scale(objectAssociatedMarker5TrainButton);
		objectAssociatedMarker5LoadButton = new JButton("Load");
		scale(objectAssociatedMarker5LoadButton);
		objectAssociatedMarker5SaveButton = new JButton("Save");
		scale(objectAssociatedMarker5SaveButton);
		objectAssociatedMarker5Pattern1Button = new JRadioButton("P1");
		scale(objectAssociatedMarker5Pattern1Button);
		objectAssociatedMarker5Pattern2Button = new JRadioButton("P2");
		scale(objectAssociatedMarker5Pattern2Button);
		objectAssociatedMarker5Pattern3Button = new JRadioButton("P3");
		scale(objectAssociatedMarker5Pattern3Button);
		objectAssociatedMarker5Pattern4Button = new JRadioButton("P4");
		scale(objectAssociatedMarker5Pattern4Button);
		objectAssociatedMarker6Button = new JRadioButton("Marker6");
		scale(objectAssociatedMarker6Button);
		objectAssociatedMarker6ColorButton = new JButton("Color");
		scale(objectAssociatedMarker6ColorButton);
		objectAssociatedMarker6ColorMLButton = new JButton("Color");
		scale(objectAssociatedMarker6ColorMLButton);
		objectAssociatedMarker6RemoveButton = new JButton("Remove");
		scale(objectAssociatedMarker6RemoveButton);
		objectAssociatedMarker6PositiveLabelButton = new JRadioButton("M+");
		scale(objectAssociatedMarker6PositiveLabelButton);
		objectAssociatedMarker6NegativeLabelButton = new JRadioButton("M-");
		scale(objectAssociatedMarker6NegativeLabelButton);
		objectAssociatedMarker6TrainButton = new JButton("Train");
		scale(objectAssociatedMarker6TrainButton);
		objectAssociatedMarker6LoadButton = new JButton("Load");
		scale(objectAssociatedMarker6LoadButton);
		objectAssociatedMarker6SaveButton = new JButton("Save");
		scale(objectAssociatedMarker6SaveButton);
		objectAssociatedMarker6Pattern1Button = new JRadioButton("P1");
		scale(objectAssociatedMarker6Pattern1Button);
		objectAssociatedMarker6Pattern2Button = new JRadioButton("P2");
		scale(objectAssociatedMarker6Pattern2Button);
		objectAssociatedMarker6Pattern3Button = new JRadioButton("P3");
		scale(objectAssociatedMarker6Pattern3Button);
		objectAssociatedMarker6Pattern4Button = new JRadioButton("P4");
		scale(objectAssociatedMarker6Pattern4Button);
		objectAssociatedMarker7Button = new JRadioButton("Marker7");
		scale(objectAssociatedMarker7Button);
		objectAssociatedMarker7ColorButton = new JButton("Color");
		scale(objectAssociatedMarker7ColorButton);
		objectAssociatedMarker7ColorMLButton = new JButton("Color");
		scale(objectAssociatedMarker7ColorMLButton);
		objectAssociatedMarker7RemoveButton = new JButton("Remove");
		scale(objectAssociatedMarker7RemoveButton);
		objectAssociatedMarker7PositiveLabelButton = new JRadioButton("M+");
		scale(objectAssociatedMarker7PositiveLabelButton);
		objectAssociatedMarker7NegativeLabelButton = new JRadioButton("M-");
		scale(objectAssociatedMarker7NegativeLabelButton);
		objectAssociatedMarker7TrainButton = new JButton("Train");
		scale(objectAssociatedMarker7TrainButton);
		objectAssociatedMarker7LoadButton = new JButton("Load");
		scale(objectAssociatedMarker7LoadButton);
		objectAssociatedMarker7SaveButton = new JButton("Save");
		scale(objectAssociatedMarker7SaveButton);
		objectAssociatedMarker7Pattern1Button = new JRadioButton("P1");
		scale(objectAssociatedMarker7Pattern1Button);
		objectAssociatedMarker7Pattern2Button = new JRadioButton("P2");
		scale(objectAssociatedMarker7Pattern2Button);
		objectAssociatedMarker7Pattern3Button = new JRadioButton("P3");
		scale(objectAssociatedMarker7Pattern3Button);
		objectAssociatedMarker7Pattern4Button = new JRadioButton("P4");
		scale(objectAssociatedMarker7Pattern4Button);

		analyzeMarkersButton = new JButton("Measurements");
		scale(analyzeMarkersButton);
		batchMarkersButton = new JButton("Batch");
		scale(batchMarkersButton);
		markerSnapshotButton = new JButton("Snapshot");
		scale(markerSnapshotButton);
		loadObjectAssociatedMarkerButton = new JButton("Load");
		scale(loadObjectAssociatedMarkerButton);
		saveObjectAssociatedMarkerButton = new JButton("Save");
		scale(saveObjectAssociatedMarkerButton);

		markersOverlay = new Overlay();
		roiListener = new RoiListener();
		keyListener = new KeyActions();

		objectsInEachClass[0] = new ArrayList<Point[]>();
		firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;

		areasInEachClass[0] = new ArrayList<Point[]>();

		for(int j = 0; j < 4; j++) {
			positiveNucleiForEachMarker[0][j] = new ArrayList<Short>();
		}
		positivelyLabelledNucleiForEachMarker[0] = new ArrayList<Short>();
		negativelyLabelledNucleiForEachMarker[0] = new ArrayList<Short>();
		featuresForEachMarker[0] = new ArrayList<double[]>();
		
		redCheck = new JRadioButton("Red");
		scale(redCheck);
		greenCheck = new JRadioButton("Green");
		scale(greenCheck);
		blueCheck = new JRadioButton("Blue");
		scale(blueCheck);
		yellowCheck = new JRadioButton("Yellow");
		scale(yellowCheck);
		magentaCheck = new JRadioButton("Magenta");
		scale(magentaCheck);
		cyanCheck = new JRadioButton("Cyan");
		scale(cyanCheck);
		orangeCheck = new JRadioButton("Orange");
		scale(orangeCheck);
		pinkCheck = new JRadioButton("Pink");
		scale(pinkCheck);
		blackCheck = new JRadioButton("Black");
		scale(blackCheck);
		grayCheck = new JRadioButton("Gray");
		scale(grayCheck);
		whiteCheck = new JRadioButton("White");
		scale(whiteCheck);

		redCheck1 = new JRadioButton("Red");
		scale(redCheck1);
		greenCheck1 = new JRadioButton("Green");
		scale(greenCheck1);
		blueCheck1 = new JRadioButton("Blue");
		scale(blueCheck1);
		yellowCheck1 = new JRadioButton("Yellow");
		scale(yellowCheck1);
		magentaCheck1 = new JRadioButton("Magenta");
		scale(magentaCheck1);
		cyanCheck1 = new JRadioButton("Cyan");
		scale(cyanCheck1);
		orangeCheck1 = new JRadioButton("Orange");
		scale(orangeCheck1);
		pinkCheck1 = new JRadioButton("Pink");
		scale(pinkCheck1);
		blackCheck1 = new JRadioButton("Black");
		scale(blackCheck1);
		grayCheck1 = new JRadioButton("Gray");
		scale(grayCheck1);
		whiteCheck1 = new JRadioButton("White");
		scale(whiteCheck1);
		redCheck2 = new JRadioButton("Red");
		scale(redCheck2);
		greenCheck2 = new JRadioButton("Green");
		scale(greenCheck2);
		blueCheck2 = new JRadioButton("Blue");
		scale(blueCheck2);
		yellowCheck2 = new JRadioButton("Yellow");
		scale(yellowCheck2);
		magentaCheck2 = new JRadioButton("Magenta");
		scale(magentaCheck2);
		cyanCheck2 = new JRadioButton("Cyan");
		scale(cyanCheck2);
		orangeCheck2 = new JRadioButton("Orange");
		scale(orangeCheck2);
		pinkCheck2 = new JRadioButton("Pink");
		scale(pinkCheck2);
		blackCheck2 = new JRadioButton("Black");
		scale(blackCheck2);
		grayCheck2 = new JRadioButton("Gray");
		scale(grayCheck2);
		whiteCheck2 = new JRadioButton("White");
		scale(whiteCheck2);
		redCheck3 = new JRadioButton("Red");
		scale(redCheck3);
		greenCheck3 = new JRadioButton("Green");
		scale(greenCheck3);
		blueCheck3 = new JRadioButton("Blue");
		scale(blueCheck3);
		yellowCheck3 = new JRadioButton("Yellow");
		scale(yellowCheck3);
		magentaCheck3 = new JRadioButton("Magenta");
		scale(magentaCheck3);
		cyanCheck3 = new JRadioButton("Cyan");
		scale(cyanCheck3);
		orangeCheck3 = new JRadioButton("Orange");
		scale(orangeCheck3);
		pinkCheck3 = new JRadioButton("Pink");
		scale(pinkCheck3);
		blackCheck3 = new JRadioButton("Black");
		scale(blackCheck3);
		grayCheck3 = new JRadioButton("Gray");
		scale(grayCheck3);
		whiteCheck3 = new JRadioButton("White");
		scale(whiteCheck3);
		redCheck4 = new JRadioButton("Red");
		scale(redCheck4);
		greenCheck4 = new JRadioButton("Green");
		scale(greenCheck4);
		blueCheck4 = new JRadioButton("Blue");
		scale(blueCheck4);
		yellowCheck4 = new JRadioButton("Yellow");
		scale(yellowCheck4);
		magentaCheck4 = new JRadioButton("Magenta");
		scale(magentaCheck4);
		cyanCheck4 = new JRadioButton("Cyan");
		scale(cyanCheck4);
		orangeCheck4 = new JRadioButton("Orange");
		scale(orangeCheck4);
		pinkCheck4 = new JRadioButton("Pink");
		scale(pinkCheck4);
		blackCheck4 = new JRadioButton("Black");
		scale(blackCheck4);
		grayCheck4 = new JRadioButton("Gray");
		scale(grayCheck4);
		whiteCheck4 = new JRadioButton("White");
		scale(whiteCheck4);

		intensityThresholdingForObjectAssociatedMarkerScrollBar = new JSlider(0, 100, 0);
		scale(intensityThresholdingForObjectAssociatedMarkerScrollBar);
		intensityThresholdingForObjectAssociatedMarkerTextArea = new JTextArea();
		scale(intensityThresholdingForObjectAssociatedMarkerTextArea);
		setIntensityThresholdForObjectAssociatedMarkerButton = new JButton("Set threshold");
		scale(setIntensityThresholdForObjectAssociatedMarkerButton);
		areaThresholdingScrollBar = new JSlider(0, 100, 35);
		scale(areaThresholdingScrollBar);
		areaThresholdingTextArea = new JTextArea();
		scale(areaThresholdingTextArea);
		setAreaThresholdButton = new JButton("Set threshold");
		scale(setAreaThresholdButton);
		okMarkerForObjectAssociatedMarkersButton = new JButton("Ok");
		scale(okMarkerForObjectAssociatedMarkersButton);
		cancelMarkerForObjectAssociatedMarkersButton = new JButton("Cancel");
		scale(cancelMarkerForObjectAssociatedMarkersButton);

		byte[] channel1cm = new byte[256], channel2cm = new byte[256], channel3cm = new byte[256];

		for (int i = 0; i < 256; i++){
			channel1cm[i] = (byte)i;
			channel2cm[i] = (byte)0;
		}
		areaColorModels[0] = new IndexColorModel(8, 256, channel1cm, channel2cm, channel2cm);
		areaColorModels[1] = new IndexColorModel(8, 256, channel2cm, channel1cm, channel2cm);
		areaColorModels[2] = new IndexColorModel(8, 256, channel2cm, channel2cm, channel1cm);
		areaColorModels[3] = new IndexColorModel(8, 256, channel1cm, channel1cm, channel2cm);
		areaColorModels[4] = new IndexColorModel(8, 256, channel1cm, channel2cm, channel1cm);
		areaColorModels[5] = new IndexColorModel(8, 256, channel2cm, channel1cm, channel1cm);
		areaColorModels[6] = new IndexColorModel(8, 256, channel1cm, channel1cm, channel1cm);

	}

	@Override
	public void run() {
		try {
			System.setProperty("sun.java2d.uiScale", "3.0");
        } catch(Exception e) {
			IJ.showMessage("Problem when changing resolution");
        }
		
		if (IJ.macroRunning()) {
			String macroParameters = Macro.getOptions();

			Macro.setOptions(macroParameters);
			String[] parameters = macroParameters.split(" ");

			String parameter1, parameter2;
			if(parameters.length==2) {
				parameter1 = parameters[0].split("=")[1];
				parameter2 = parameters[1].split("=")[1];
			}
			else {
				String[] parameter1_tmp1, parameter1_tmp2, parameter2_tmp1, parameter2_tmp2;
				parameter1_tmp1 = parameters[1].split("=");
				parameter1_tmp2 = parameter1_tmp1[1].split("\\[");
				parameter1 = parameter1_tmp2[1].split("]")[0];
				parameter2_tmp1 = parameters[2].split("=");
				parameter2_tmp2 = parameter2_tmp1[1].split("\\[");
				parameter2 = parameter2_tmp2[1].split("]")[0];
			}

			Opener opener = new Opener();
			displayImage = opener.openImage(parameter1);

			int[] dims = displayImage.getDimensions();

			if((dims[2]==1)&&(dims[3]==1)&&(dims[4]==1)) {
				ImageConverter ic = new ImageConverter(displayImage);
				ic.convertToRGB();
			}
			if(displayImage.getType()==4) {
				displayImage = CompositeConverter.makeComposite(displayImage);
				dims = displayImage.getDimensions();
			}
			if(dims[2]==1) {
				if((dims[3]>1)&&(dims[4]==1)) {
					displayImage = HyperStackConverter.toHyperStack(displayImage, dims[3], 1, 1);
				}
				if((dims[4]>1)&&(dims[3]==1)) {
					displayImage = HyperStackConverter.toHyperStack(displayImage, dims[4], 1, 1);
				}
				dims = displayImage.getDimensions();
			}

			numOfChannels = (byte)dims[2];

			if(numOfChannels>7) {
				IJ.showMessage("Too many channels", "Images cannot exceed 7 channels");
				return;
			}
			if((dims[3]>1)||(dims[4]>1)) {
				IJ.showMessage("2D image", "Only 2D multi-channel images are accepted");
				return;
			}

			roiFlag = new short [displayImage.getWidth()][displayImage.getHeight()][3];
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					roiFlag[x][y][0] = -1;
					roiFlag[x][y][1] = -1;
					roiFlag[x][y][2] = -1;
				}
			}

			areaFlag = new short [displayImage.getWidth()][displayImage.getHeight()][3];
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					for(int i=0; i<3; i++)
					{
						areaFlag[x][y][i] = -1;
					}
				}
			}

			//Build GUI
			//win = new CustomWindow(displayImage);
			//win.pack();
			repaintWindow();
			if((dims[2]==1)&&(dims[3]==1)&&(dims[4]==1)) {
				IJ.run("Grays");
			}

			ImagePlus segmentedImage = opener.openImage(parameter2);
			loadNucleiSegmentations(segmentedImage);
		}
		else {
			if (null == WindowManager.getCurrentImage()) 
			{
				displayImage = IJ.openImage();
				if (null == displayImage) return; // user canceled open dialog
			}
			else 		
			{
				displayImage = new ImagePlus("Annotater",WindowManager.getCurrentImage().getProcessor().duplicate());
			}
			int[] dims = displayImage.getDimensions();

			if(displayImage.getType()==4) {
				displayImage = CompositeConverter.makeComposite(displayImage);
				dims = displayImage.getDimensions();
			}
			if(dims[2]==1) {
				if((dims[3]>1)&&(dims[4]==1)) {
					displayImage = HyperStackConverter.toHyperStack(displayImage, dims[3], 1, 1);
				}
				if((dims[4]>1)&&(dims[3]==1)) {
					displayImage = HyperStackConverter.toHyperStack(displayImage, dims[4], 1, 1);
				}
				dims = displayImage.getDimensions();
			}

			numOfChannels = (byte)dims[2];

			if(numOfChannels>7) {
				IJ.showMessage("Too many channels", "Images cannot exceed 7 channels");
				return;
			}
			if((dims[3]>1)||(dims[4]>1)) {
				IJ.showMessage("2D image", "Only 2D multi-channel images are accepted");
				return;
			}
			//originalLUT = displayImage.getLuts();

			roiFlag = new short [displayImage.getWidth()][displayImage.getHeight()][3];
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					for(int i=0; i<3; i++)
					{
						roiFlag[x][y][i] = -1;
					}
				}
			}

			areaFlag = new short [displayImage.getWidth()][displayImage.getHeight()][3];
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					for(int i=0; i<3; i++)
					{
						areaFlag[x][y][i] = -1;
					}
				}
			}

			//Build GUI
			repaintWindow();
			if((dims[2]==1)&&(dims[3]==1)&&(dims[4]==1)) {
				IJ.run("Grays");
			}

		}

	}

	/**
	 * Roi color changing functions
	 */
	byte getSelectedClassColor() {
		byte colorCode = 0;
		if(redCheck.isSelected()) {colorCode = 0;}
		if(greenCheck.isSelected()) {colorCode = 1;}
		if(blueCheck.isSelected()) {colorCode = 2;}
		if(yellowCheck.isSelected()) {colorCode = 3;}
		if(magentaCheck.isSelected()) {colorCode = 4;}
		if(cyanCheck.isSelected()) {colorCode = 5;}
		if(orangeCheck.isSelected()) {colorCode = 6;}
		if(pinkCheck.isSelected()) {colorCode = 7;}
		if(blackCheck.isSelected()) {colorCode = 8;}
		if(grayCheck.isSelected()) {colorCode = 9;}
		if(whiteCheck.isSelected()) {colorCode = 10;}
		return colorCode;
	}
	byte getSelectedAreaColor() {
		byte colorCode = 0;
		if(redCheck.isSelected()) {colorCode = 0;}
		if(greenCheck.isSelected()) {colorCode = 1;}
		if(blueCheck.isSelected()) {colorCode = 2;}
		if(yellowCheck.isSelected()) {colorCode = 3;}
		if(magentaCheck.isSelected()) {colorCode = 4;}
		if(cyanCheck.isSelected()) {colorCode = 5;}
		if(whiteCheck.isSelected()) {colorCode = 6;}
		return colorCode;
	}
	void updateRoiClassColor(int consideredClass) {
		byte selectedColor = getSelectedClassColor(),alreadyUsedColorClass=-1;
		if(selectedColor!=classColors[consideredClass]) {
			for(byte i=0;i<classColors.length;i++) {
				if(selectedColor==classColors[i]) {
					alreadyUsedColorClass = i;
				}
			}
		}
		if(alreadyUsedColorClass>(-1)) {
			IJ.showMessage("Color not available", "The selected color is already used for class " + (alreadyUsedColorClass+1));
		}
		else{
			classColors[consideredClass] = selectedColor;
			if(!objectDisplayFlag){addObjectsToOverlay();visualizeObjectsButton1.setSelected(true);visualizeObjectsButton2.setSelected(true);}
			addObjectsToOverlay();
		}
	}
	void updateRoiAreaColor(int consideredArea) {
		byte selectedColor = getSelectedAreaColor(),alreadyUsedColorClass=-1;
		if(selectedColor!=areaColors[consideredArea]) {
			for(byte i=0;i<areaColors.length;i++) {
				if(selectedColor==areaColors[i]) {
					alreadyUsedColorClass = i;
				}
			}
		}
		if(alreadyUsedColorClass>(-1)) {
			IJ.showMessage("Color not available", "The selected color is already used for area " + (alreadyUsedColorClass+1));
		}
		else{
			areaColors[consideredArea] = selectedColor;
			if(!areaDisplayFlag){addAreasToOverlay();visualizeAreasButton1.setSelected(true);visualizeAreasButton2.setSelected(true);}
			addAreasToOverlay();
		}
	}

	/**
	 * Marker color changing functions
	 */
	byte getPattern1ClassColor() {
		byte colorCode = 0;
		if(redCheck1.isSelected()) {colorCode = 0;}
		if(greenCheck1.isSelected()) {colorCode = 1;}
		if(blueCheck1.isSelected()) {colorCode = 2;}
		if(yellowCheck1.isSelected()) {colorCode = 3;}
		if(magentaCheck1.isSelected()) {colorCode = 4;}
		if(cyanCheck1.isSelected()) {colorCode = 5;}
		if(orangeCheck1.isSelected()) {colorCode = 6;}
		if(pinkCheck1.isSelected()) {colorCode = 7;}
		if(blackCheck1.isSelected()) {colorCode = 8;}
		if(grayCheck1.isSelected()) {colorCode = 9;}
		if(whiteCheck1.isSelected()) {colorCode = 10;}
		return colorCode;
	}
	byte getPattern2ClassColor() {
		byte colorCode = 0;
		if(redCheck2.isSelected()) {colorCode = 0;}
		if(greenCheck2.isSelected()) {colorCode = 1;}
		if(blueCheck2.isSelected()) {colorCode = 2;}
		if(yellowCheck2.isSelected()) {colorCode = 3;}
		if(magentaCheck2.isSelected()) {colorCode = 4;}
		if(cyanCheck2.isSelected()) {colorCode = 5;}
		if(orangeCheck2.isSelected()) {colorCode = 6;}
		if(pinkCheck2.isSelected()) {colorCode = 7;}
		if(blackCheck2.isSelected()) {colorCode = 8;}
		if(grayCheck2.isSelected()) {colorCode = 9;}
		if(whiteCheck2.isSelected()) {colorCode = 10;}
		return colorCode;
	}
	byte getPattern3ClassColor() {
		byte colorCode = 0;
		if(redCheck3.isSelected()) {colorCode = 0;}
		if(greenCheck3.isSelected()) {colorCode = 1;}
		if(blueCheck3.isSelected()) {colorCode = 2;}
		if(yellowCheck3.isSelected()) {colorCode = 3;}
		if(magentaCheck3.isSelected()) {colorCode = 4;}
		if(cyanCheck3.isSelected()) {colorCode = 5;}
		if(orangeCheck3.isSelected()) {colorCode = 6;}
		if(pinkCheck3.isSelected()) {colorCode = 7;}
		if(blackCheck3.isSelected()) {colorCode = 8;}
		if(grayCheck3.isSelected()) {colorCode = 9;}
		if(whiteCheck3.isSelected()) {colorCode = 10;}
		return colorCode;
	}
	byte getPattern4ClassColor() {
		byte colorCode = 0;
		if(redCheck4.isSelected()) {colorCode = 0;}
		if(greenCheck4.isSelected()) {colorCode = 1;}
		if(blueCheck4.isSelected()) {colorCode = 2;}
		if(yellowCheck4.isSelected()) {colorCode = 3;}
		if(magentaCheck4.isSelected()) {colorCode = 4;}
		if(cyanCheck4.isSelected()) {colorCode = 5;}
		if(orangeCheck4.isSelected()) {colorCode = 6;}
		if(pinkCheck4.isSelected()) {colorCode = 7;}
		if(blackCheck4.isSelected()) {colorCode = 8;}
		if(grayCheck4.isSelected()) {colorCode = 9;}
		if(whiteCheck4.isSelected()) {colorCode = 10;}
		return colorCode;
	}
	void updatePatternColor(int consideredMarker) {
		byte colorPattern1 = getPattern1ClassColor(), colorPattern2 = getPattern2ClassColor(), colorPattern3 = getPattern3ClassColor(), colorPattern4 = getPattern4ClassColor();
		if(colorPattern1==colorPattern2) {
			IJ.showMessage("Patterns 1 and 2 cannot have the same color");
		}
		else if(colorPattern1==colorPattern3) {
			IJ.showMessage("Patterns 1 and 3 cannot have the same color");
		}
		else if(colorPattern1==colorPattern4) {
			IJ.showMessage("Patterns 1 and 4 cannot have the same color");
		}
		else if(colorPattern2==colorPattern3) {
			IJ.showMessage("Patterns 2 and 3 cannot have the same color");
		}
		else if(colorPattern2==colorPattern4) {
			IJ.showMessage("Patterns 2 and 4 cannot have the same color");
		}
		else if(colorPattern3==colorPattern4) {
			IJ.showMessage("Patterns 3 and 4 cannot have the same color");
		}
		else {
			boolean change = false;
			if(colorPattern1!=objectAssociatedMarkersColors[consideredMarker][0]) {objectAssociatedMarkersColors[consideredMarker][0] = colorPattern1;change=true;}
			if(colorPattern2!=objectAssociatedMarkersColors[consideredMarker][1]) {objectAssociatedMarkersColors[consideredMarker][1] = colorPattern2;change=true;}
			if(colorPattern3!=objectAssociatedMarkersColors[consideredMarker][2]) {objectAssociatedMarkersColors[consideredMarker][2] = colorPattern3;change=true;}
			if(colorPattern4!=objectAssociatedMarkersColors[consideredMarker][3]) {objectAssociatedMarkersColors[consideredMarker][3] = colorPattern4;change=true;}
			if(change) {
				removeMarkersFromOverlay();
				activateCurrentNucleiMarkerOverlays(consideredMarker);
			}
		}
	}
	void updateMLColor(int consideredMarker) {
		byte colorPositiveLabel = getPattern1ClassColor(), colorNegativeLabel = getPattern2ClassColor(), colorEstimatedLabel = getPattern3ClassColor();
		if(colorPositiveLabel==colorNegativeLabel) {
			IJ.showMessage("Positively and negatively labelled markers cannot have the same color");
		}
		else if(colorPositiveLabel==colorEstimatedLabel) {
			IJ.showMessage("Positively labelled and positively estimated markers cannot have the same color");
		}
		else if(colorNegativeLabel==colorEstimatedLabel) {
			IJ.showMessage("Negatively labelled and positively estimated markers cannot have the same color");
		}
		else {
			boolean change = false;
			if(colorPositiveLabel!=objectAssociatedMarkersMLColors[consideredMarker][0]) {objectAssociatedMarkersMLColors[consideredMarker][0] = colorPositiveLabel;change=true;}
			if(colorNegativeLabel!=objectAssociatedMarkersMLColors[consideredMarker][1]) {objectAssociatedMarkersMLColors[consideredMarker][1] = colorNegativeLabel;change=true;}
			if(colorEstimatedLabel!=objectAssociatedMarkersMLColors[consideredMarker][2]) {objectAssociatedMarkersMLColors[consideredMarker][2] = colorEstimatedLabel;change=true;}
			if(change) {
				removeMarkersFromOverlay();
				activateCurrentNucleiMarkerOverlays(consideredMarker);
			}
		}
	}
	/** get image with classes as overlays for figures/presentations */
	void takeClassSnapshot() {
		ImagePlus snapshot = new Duplicator().run(displayImage);
		if(overlay.size()>0) {snapshot.setOverlay(overlay);}
		snapshot.updateAndDraw();
		snapshot.show();
		IJ.run("Flatten");
	}
	/** get image with classes as overlays for figures/presentations */
	void takeClassSnapshot(String outputFile) {
		removeMarkersFromOverlay();
		ImagePlus snapshot = new Duplicator().run(displayImage);
		if(overlay.size()>0) {snapshot.setOverlay(overlay);}
		snapshot.updateAndDraw();
		IJ.run(snapshot, "Flatten", "");
		IJ.save(snapshot, outputFile);

	}
	/**
	 * Listeners
	 */
	private ActionListener listener = new ActionListener() {
		public void actionPerformed(final ActionEvent e) {
			// listen to the buttons on separate threads not to block
			// the event dispatch thread
			exec.submit(new Runnable() {
				public void run() 
				{
					if(e.getSource() == objectsAnnotationButton){
						updateModeRadioButtons(0);
					}
					else if(e.getSource() == markerAnnotationButton){
						updateModeRadioButtons(1);
					}
					else if(e.getSource() == newObjectButton){
						updateRadioButtons(0);
					}
					else if(e.getSource() == removeObjectButton){
						updateRadioButtons(1);
					}
					else if(e.getSource() == mergeObjectsButton){
						updateRadioButtons(2);
					}
					else if(e.getSource() == splitObjectsButton){
						updateRadioButtons(3);
					}
					else if(e.getSource() == swapObjectClassButton){
						updateRadioButtons(4);
					}
					else if(e.getSource() == addClassButton){
						addNewClass();
						updateClassesButtons(numOfClasses-1);
					}
					else if(e.getSource() == class1Button){
						updateClassesButtons(0);
					}
					else if(e.getSource() == class2Button){
						updateClassesButtons(1);
					}
					else if(e.getSource() == class3Button){
						updateClassesButtons(2);
					}
					else if(e.getSource() == class4Button){
						updateClassesButtons(3);
					}
					else if(e.getSource() == class5Button){
						updateClassesButtons(4);
					}
					else if(e.getSource() == class1ColorButton){
						boolean ok = updateRoiClassColorWindow(0);
						if(ok) {updateRoiClassColor(0);}							
					}
					else if(e.getSource() == class1RemoveButton){
						removeClass(0);
					}
					else if(e.getSource() == class2ColorButton){
						boolean ok = updateRoiClassColorWindow(1);
						if(ok) {updateRoiClassColor(1);}
					}
					else if(e.getSource() == class2RemoveButton){
						removeClass(1);
					}
					else if(e.getSource() == class3ColorButton){
						boolean ok = updateRoiClassColorWindow(2);
						if(ok) {updateRoiClassColor(2);}
					}
					else if(e.getSource() == class3RemoveButton){
						removeClass(2);
					}
					else if(e.getSource() == class4ColorButton){
						boolean ok = updateRoiClassColorWindow(3);
						if(ok) {updateRoiClassColor(3);}
					}
					else if(e.getSource() == class4RemoveButton){
						removeClass(3);
					}
					else if(e.getSource() == class5ColorButton){
						boolean ok = updateRoiClassColorWindow(4);
						if(ok) {updateRoiClassColor(4);}
					}
					else if(e.getSource() == class5RemoveButton){
						removeClass(4);
					}
					else if(e.getSource() == newAreaButton){
						updateRadioButtons(5);
					}
					else if(e.getSource() == removeAreaButton){
						updateRadioButtons(6);
					}
					else if(e.getSource() == swapAreaClassButton){
						updateRadioButtons(7);
					}
					else if(e.getSource() == addAreaButton){
						addNewArea();
						updateAreaButtons(numOfAreas-1);
					}
					else if(e.getSource() == area1Button){
						updateAreaButtons(0);
					}
					else if(e.getSource() == area2Button){
						updateAreaButtons(1);
					}
					else if(e.getSource() == area3Button){
						updateAreaButtons(2);
					}
					else if(e.getSource() == area4Button){
						updateAreaButtons(3);
					}
					else if(e.getSource() == area5Button){
						updateAreaButtons(4);
					}
					else if(e.getSource() == area1ColorButton){
						boolean ok = updateAreaColorWindow(0);
						if(ok) {updateRoiAreaColor(0);}							
					}
					else if(e.getSource() == area1RemoveButton){
						removeWholeArea(0);
					}
					else if(e.getSource() == area2ColorButton){
						boolean ok = updateAreaColorWindow(1);
						if(ok) {updateRoiAreaColor(1);}							
					}
					else if(e.getSource() == area2RemoveButton){
						removeWholeArea(1);
					}
					else if(e.getSource() == area3ColorButton){
						boolean ok = updateAreaColorWindow(2);
						if(ok) {updateRoiAreaColor(2);}							
					}
					else if(e.getSource() == area3RemoveButton){
						removeWholeArea(2);
					}
					else if(e.getSource() == area4ColorButton){
						boolean ok = updateAreaColorWindow(3);
						if(ok) {updateRoiAreaColor(3);}							
					}
					else if(e.getSource() == area4RemoveButton){
						removeWholeArea(3);
					}
					else if(e.getSource() == area5ColorButton){
						boolean ok = updateAreaColorWindow(4);
						if(ok) {updateRoiAreaColor(4);}							
					}
					else if(e.getSource() == area5RemoveButton){
						removeWholeArea(4);
					}
					else if(e.getSource() == analyzeClassesButton){
						classesMeasurements();
					}
					else if(e.getSource() == classSnapshotButton){
						takeClassSnapshot();
					}
					else if(e.getSource() == visualizeChannel1Button1){
						updateVisualizeChannelButtons1((byte)0);
					}
					else if(e.getSource() == visualizeChannel2Button1){
						updateVisualizeChannelButtons1((byte)1);
					}
					else if(e.getSource() == visualizeChannel3Button1){
						updateVisualizeChannelButtons1((byte)2);
					}
					else if(e.getSource() == visualizeChannel4Button1){
						updateVisualizeChannelButtons1((byte)3);
					}
					else if(e.getSource() == visualizeChannel5Button1){
						updateVisualizeChannelButtons1((byte)4);
					}
					else if(e.getSource() == visualizeChannel6Button1){
						updateVisualizeChannelButtons1((byte)5);
					}
					else if(e.getSource() == visualizeChannel7Button1){
						updateVisualizeChannelButtons1((byte)6);
					}
					else if(e.getSource() == visualizeChannel1onlyButton1){
						updateVisualizeChannelButtons1((byte)10);
					}
					else if(e.getSource() == visualizeChannel2onlyButton1){
						updateVisualizeChannelButtons1((byte)11);
					}
					else if(e.getSource() == visualizeChannel3onlyButton1){
						updateVisualizeChannelButtons1((byte)12);
					}
					else if(e.getSource() == visualizeChannel4onlyButton1){
						updateVisualizeChannelButtons1((byte)13);
					}
					else if(e.getSource() == visualizeChannel5onlyButton1){
						updateVisualizeChannelButtons1((byte)14);
					}
					else if(e.getSource() == visualizeChannel6onlyButton1){
						updateVisualizeChannelButtons1((byte)15);
					}
					else if(e.getSource() == visualizeChannel7onlyButton1){
						updateVisualizeChannelButtons1((byte)16);
					}
					else if(e.getSource() == visualizeAllChannelsButton1){
						updateVisualizeChannelButtons1((byte)20);
					}
					else if(e.getSource() == visualizeChannel1Button2){
						updateVisualizeChannelButtons2((byte)0);
					}
					else if(e.getSource() == visualizeChannel2Button2){
						updateVisualizeChannelButtons2((byte)1);
					}
					else if(e.getSource() == visualizeChannel3Button2){
						updateVisualizeChannelButtons2((byte)2);
					}
					else if(e.getSource() == visualizeChannel4Button2){
						updateVisualizeChannelButtons2((byte)3);
					}
					else if(e.getSource() == visualizeChannel5Button2){
						updateVisualizeChannelButtons2((byte)4);
					}
					else if(e.getSource() == visualizeChannel6Button2){
						updateVisualizeChannelButtons2((byte)5);
					}
					else if(e.getSource() == visualizeChannel7Button2){
						updateVisualizeChannelButtons2((byte)6);
					}
					else if(e.getSource() == visualizeChannel1onlyButton2){
						updateVisualizeChannelButtons2((byte)10);
					}
					else if(e.getSource() == visualizeChannel2onlyButton2){
						updateVisualizeChannelButtons2((byte)11);
					}
					else if(e.getSource() == visualizeChannel3onlyButton2){
						updateVisualizeChannelButtons2((byte)12);
					}
					else if(e.getSource() == visualizeChannel4onlyButton2){
						updateVisualizeChannelButtons2((byte)13);
					}
					else if(e.getSource() == visualizeChannel5onlyButton2){
						updateVisualizeChannelButtons2((byte)14);
					}
					else if(e.getSource() == visualizeChannel6onlyButton2){
						updateVisualizeChannelButtons2((byte)15);
					}
					else if(e.getSource() == visualizeChannel7onlyButton2){
						updateVisualizeChannelButtons2((byte)16);
					}
					else if(e.getSource() == visualizeAllChannelsButton2){
						updateVisualizeChannelButtons2((byte)20);
					}
					else if(e.getSource() == visualizeObjectsButton1){
						if(visualizeObjectsButton1.isSelected()){
							addObjectsToOverlay();
							//displayImage.setOverlay(overlay);
							//displayImage.updateAndDraw();
						}
						else{
							removeObjectsFromOverlay();
						}
					}
					else if(e.getSource() == visualizeAreasButton1){
						if(visualizeAreasButton1.isSelected()){
							addAreasToOverlay();
						}
						else{
							removeAreasFromOverlay();
						}
					}
					else if(e.getSource() == visualizeObjectsButton2){
						if(visualizeObjectsButton2.isSelected()){
							addObjectsToOverlay();
						}
						else{
							removeObjectsFromOverlay();
						}
					}
					else if(e.getSource() == visualizeAreasButton2){
						if(visualizeAreasButton2.isSelected()){
							addAreasToOverlay();
						}
						else{
							removeAreasFromOverlay();
						}
					}
					else if(e.getSource() == addObjectAssociatedMarkerButton){
						if(objectsInEachClass[0].size()==0) {
							IJ.showMessage("Define nuclei before identifying markers associated with the nuclei");
						}
						else {
							if(!objectDisplayFlag){addObjectsToOverlay();visualizeObjectsButton2.setSelected(true);}
							initializeMarkerButtons();
							boolean okNbMarkers = addNewMarker();
							if(okNbMarkers) {
								boolean ok = addObjectAssociatedMarkerWindow();
								if(!ok) {deleteObjectAssociatedMarker(numOfObjectAssociatedMarkers-1);}
							}
						}
					}
					else if(e.getSource() == setIntensityThresholdForObjectAssociatedMarkerButton){
						addObjectAssociatedIntensityThresholdingWindow();
					}
					else if(e.getSource() == setAreaThresholdButton){
						addAreaThresholdingWindow();
					}
					else if(e.getSource() == okMarkerForObjectAssociatedMarkersButton){
						visualizeObjectsButton2.setSelected(true);
						addObjectsToOverlay();
						currentObjectAssociatedMarker=-1;
						updateModeRadioButtons(1);
						updateAnnotateObjectAssociatedMarker(numOfObjectAssociatedMarkers-1,false);
						okMarkerForObjectAssociatedMarkersButton.removeActionListener(listener);
						cancelMarkerForObjectAssociatedMarkersButton.removeActionListener(listener);
						setIntensityThresholdForObjectAssociatedMarkerButton.removeActionListener(listener);
						for( ChangeListener al : intensityThresholdingForObjectAssociatedMarkerScrollBar.getChangeListeners() ) {intensityThresholdingForObjectAssociatedMarkerScrollBar.removeChangeListener( al );}
					}
					else if(e.getSource() == cancelMarkerForObjectAssociatedMarkersButton){
						currentMode = 1;
						deleteObjectAssociatedMarker(numOfObjectAssociatedMarkers-1);
						okMarkerForObjectAssociatedMarkersButton.removeActionListener(listener);
						cancelMarkerForObjectAssociatedMarkersButton.removeActionListener(listener);
						setIntensityThresholdForObjectAssociatedMarkerButton.removeActionListener(listener);
						for( ChangeListener al : intensityThresholdingForObjectAssociatedMarkerScrollBar.getChangeListeners() ) {intensityThresholdingForObjectAssociatedMarkerScrollBar.removeChangeListener( al );}
					}
					else if(e.getSource() == batchClassesMeasurementsButton) {
						batchProcessing(0);
					}
					else if(e.getSource() == batchMarkersButton) {
						batchProcessing(1);
					}
					else if(e.getSource() == objectAssociatedMarker1Button){
						updateAnnotateObjectAssociatedMarker(0,false);
					}
					else if(e.getSource() == objectAssociatedMarker2Button){
						updateAnnotateObjectAssociatedMarker(1,false);
					}
					else if(e.getSource() == objectAssociatedMarker3Button){
						updateAnnotateObjectAssociatedMarker(2,false);
					}
					else if(e.getSource() == objectAssociatedMarker4Button){
						updateAnnotateObjectAssociatedMarker(3,false);
					}
					else if(e.getSource() == objectAssociatedMarker5Button){
						updateAnnotateObjectAssociatedMarker(4,false);
					}
					else if(e.getSource() == objectAssociatedMarker6Button){
						updateAnnotateObjectAssociatedMarker(5,false);
					}
					else if(e.getSource() == objectAssociatedMarker7Button){
						updateAnnotateObjectAssociatedMarker(6,false);
					}
					else if(e.getSource() == objectAssociatedMarker1ColorButton){
						if(methodToIdentifyObjectAssociatedMarkers[0]<2){
							boolean ok = updatePatternColorsWindow(0);
							if(ok) {updatePatternColor(0);}
						}
						else{
							boolean ok = updateMLColorsWindow(0);
							if(ok) {updateMLColor(0);}
						}
					}
					else if(e.getSource() == objectAssociatedMarker1RemoveButton){
						removeObjectAssociatedMarker(0);
					}
					else if(e.getSource() == objectAssociatedMarker2ColorButton){
						if(methodToIdentifyObjectAssociatedMarkers[1]<2){
							boolean ok = updatePatternColorsWindow(1);
							if(ok) {updatePatternColor(1);}
						}
					}
					else if(e.getSource() == objectAssociatedMarker2RemoveButton){
						removeObjectAssociatedMarker(1);
					}
					else if(e.getSource() == objectAssociatedMarker3ColorButton){
						if(methodToIdentifyObjectAssociatedMarkers[2]<2){
							boolean ok = updatePatternColorsWindow(2);
							if(ok) {updatePatternColor(2);}
						}
					}
					else if(e.getSource() == objectAssociatedMarker3RemoveButton){
						removeObjectAssociatedMarker(2);
					}
					else if(e.getSource() == objectAssociatedMarker4ColorButton){
						if(methodToIdentifyObjectAssociatedMarkers[3]<2){
							boolean ok = updatePatternColorsWindow(3);
							if(ok) {updatePatternColor(3);}
						}
					}
					else if(e.getSource() == objectAssociatedMarker4RemoveButton){
						removeObjectAssociatedMarker(3);
					}
					else if(e.getSource() == objectAssociatedMarker5ColorButton){
						if(methodToIdentifyObjectAssociatedMarkers[4]<2){
							boolean ok = updatePatternColorsWindow(4);
							if(ok) {updatePatternColor(4);}
						}
					}
					else if(e.getSource() == objectAssociatedMarker5RemoveButton){
						removeObjectAssociatedMarker(4);
					}
					else if(e.getSource() == objectAssociatedMarker6ColorButton){
						if(methodToIdentifyObjectAssociatedMarkers[5]<2){
							boolean ok = updatePatternColorsWindow(5);
							if(ok) {updatePatternColor(5);}
						}
					}
					else if(e.getSource() == objectAssociatedMarker6RemoveButton){
						removeObjectAssociatedMarker(5);
					}
					else if(e.getSource() == objectAssociatedMarker7ColorButton){
						if(methodToIdentifyObjectAssociatedMarkers[6]<2){
							boolean ok = updatePatternColorsWindow(6);
							if(ok) {updatePatternColor(6);}
						}
					}
					else if(e.getSource() == objectAssociatedMarker7RemoveButton){
						removeObjectAssociatedMarker(6);
					}
					else if(e.getSource() == objectAssociatedMarker1Pattern1Button){
						updateAnnotateChannelPatternButtons(0);
					}
					else if(e.getSource() == objectAssociatedMarker1Pattern2Button){
						updateAnnotateChannelPatternButtons(1);
					}
					else if(e.getSource() == objectAssociatedMarker1Pattern3Button){
						updateAnnotateChannelPatternButtons(2);
					}
					else if(e.getSource() == objectAssociatedMarker1Pattern4Button){
						updateAnnotateChannelPatternButtons(3);
					}
					else if(e.getSource() == objectAssociatedMarker1PositiveLabelButton){
						updateAnnotateChannelPatternButtons(4);
					}
					else if(e.getSource() == objectAssociatedMarker1NegativeLabelButton){
						updateAnnotateChannelPatternButtons(5);
					}
					else if(e.getSource() == objectAssociatedMarker2Pattern1Button){
						updateAnnotateChannelPatternButtons(6);
					}
					else if(e.getSource() == objectAssociatedMarker2Pattern2Button){
						updateAnnotateChannelPatternButtons(7);
					}
					else if(e.getSource() == objectAssociatedMarker2Pattern3Button){
						updateAnnotateChannelPatternButtons(8);
					}
					else if(e.getSource() == objectAssociatedMarker2Pattern4Button){
						updateAnnotateChannelPatternButtons(9);
					}
					else if(e.getSource() == objectAssociatedMarker2PositiveLabelButton){
						updateAnnotateChannelPatternButtons(10);
					}
					else if(e.getSource() == objectAssociatedMarker2NegativeLabelButton){
						updateAnnotateChannelPatternButtons(11);
					}
					else if(e.getSource() == objectAssociatedMarker3Pattern1Button){
						updateAnnotateChannelPatternButtons(12);
					}
					else if(e.getSource() == objectAssociatedMarker3Pattern2Button){
						updateAnnotateChannelPatternButtons(13);
					}
					else if(e.getSource() == objectAssociatedMarker3Pattern3Button){
						updateAnnotateChannelPatternButtons(14);
					}
					else if(e.getSource() == objectAssociatedMarker3Pattern4Button){
						updateAnnotateChannelPatternButtons(15);
					}
					else if(e.getSource() == objectAssociatedMarker3PositiveLabelButton){
						updateAnnotateChannelPatternButtons(16);
					}
					else if(e.getSource() == objectAssociatedMarker3NegativeLabelButton){
						updateAnnotateChannelPatternButtons(17);
					}
					else if(e.getSource() == objectAssociatedMarker4Pattern1Button){
						updateAnnotateChannelPatternButtons(18);
					}
					else if(e.getSource() == objectAssociatedMarker4Pattern2Button){
						updateAnnotateChannelPatternButtons(19);
					}
					else if(e.getSource() == objectAssociatedMarker4Pattern3Button){
						updateAnnotateChannelPatternButtons(20);
					}
					else if(e.getSource() == objectAssociatedMarker4Pattern4Button){
						updateAnnotateChannelPatternButtons(21);
					}
					else if(e.getSource() == objectAssociatedMarker4PositiveLabelButton){
						updateAnnotateChannelPatternButtons(22);
					}
					else if(e.getSource() == objectAssociatedMarker4NegativeLabelButton){
						updateAnnotateChannelPatternButtons(23);
					}
					else if(e.getSource() == objectAssociatedMarker5Pattern1Button){
						updateAnnotateChannelPatternButtons(24);
					}
					else if(e.getSource() == objectAssociatedMarker5Pattern2Button){
						updateAnnotateChannelPatternButtons(25);
					}
					else if(e.getSource() == objectAssociatedMarker5Pattern3Button){
						updateAnnotateChannelPatternButtons(26);
					}
					else if(e.getSource() == objectAssociatedMarker5Pattern4Button){
						updateAnnotateChannelPatternButtons(27);
					}
					else if(e.getSource() == objectAssociatedMarker5PositiveLabelButton){
						updateAnnotateChannelPatternButtons(28);
					}
					else if(e.getSource() == objectAssociatedMarker5NegativeLabelButton){
						updateAnnotateChannelPatternButtons(29);
					}
					else if(e.getSource() == objectAssociatedMarker6Pattern1Button){
						updateAnnotateChannelPatternButtons(30);
					}
					else if(e.getSource() == objectAssociatedMarker6Pattern2Button){
						updateAnnotateChannelPatternButtons(31);
					}
					else if(e.getSource() == objectAssociatedMarker6Pattern3Button){
						updateAnnotateChannelPatternButtons(32);
					}
					else if(e.getSource() == objectAssociatedMarker6Pattern4Button){
						updateAnnotateChannelPatternButtons(33);
					}
					else if(e.getSource() == objectAssociatedMarker6PositiveLabelButton){
						updateAnnotateChannelPatternButtons(34);
					}
					else if(e.getSource() == objectAssociatedMarker6NegativeLabelButton){
						updateAnnotateChannelPatternButtons(35);
					}
					else if(e.getSource() == objectAssociatedMarker7Pattern1Button){
						updateAnnotateChannelPatternButtons(36);
					}
					else if(e.getSource() == objectAssociatedMarker7Pattern2Button){
						updateAnnotateChannelPatternButtons(37);
					}
					else if(e.getSource() == objectAssociatedMarker7Pattern3Button){
						updateAnnotateChannelPatternButtons(38);
					}
					else if(e.getSource() == objectAssociatedMarker7Pattern4Button){
						updateAnnotateChannelPatternButtons(39);
					}
					else if(e.getSource() == objectAssociatedMarker7PositiveLabelButton){
						updateAnnotateChannelPatternButtons(40);
					}
					else if(e.getSource() == objectAssociatedMarker7NegativeLabelButton){
						updateAnnotateChannelPatternButtons(41);
					}
					else if(e.getSource() == objectAssociatedMarker1TrainButton){
						if(currentObjectAssociatedMarker!=0){
							updateAnnotateChannelPatternButtons(4);
						}
						removeMarkersFromOverlay();
						removeObjectAssociatedMarkerForML(0);
						train(0);
					}
					else if(e.getSource() == objectAssociatedMarker1SaveButton){
						updateAnnotateChannelPatternButtons(4);
						saveDataForLogisticRegression(0);
					}
					else if(e.getSource() == objectAssociatedMarker1LoadButton){
						updateAnnotateChannelPatternButtons(4);
						loadDataForLogisticRegression(0);
					}
					else if(e.getSource() == objectAssociatedMarker2TrainButton){
						if(currentObjectAssociatedMarker!=1){
							updateAnnotateChannelPatternButtons(10);
						}
						removeMarkersFromOverlay();
						removeObjectAssociatedMarkerForML(1);
						train(1);
					}
					else if(e.getSource() == objectAssociatedMarker2SaveButton){
						updateAnnotateChannelPatternButtons(10);
						saveDataForLogisticRegression(1);
					}
					else if(e.getSource() == objectAssociatedMarker2LoadButton){
						updateAnnotateChannelPatternButtons(10);
						loadDataForLogisticRegression(1);
					}
					else if(e.getSource() == objectAssociatedMarker3TrainButton){
						if(currentObjectAssociatedMarker!=2){
							updateAnnotateChannelPatternButtons(16);
						}
						removeMarkersFromOverlay();
						removeObjectAssociatedMarkerForML(2);
						train(2);
					}
					else if(e.getSource() == objectAssociatedMarker3SaveButton){
						updateAnnotateChannelPatternButtons(16);
						saveDataForLogisticRegression(2);
					}
					else if(e.getSource() == objectAssociatedMarker3LoadButton){
						updateAnnotateChannelPatternButtons(16);
						loadDataForLogisticRegression(2);
					}
					else if(e.getSource() == objectAssociatedMarker4TrainButton){
						if(currentObjectAssociatedMarker!=3){
							updateAnnotateChannelPatternButtons(22);
						}
						removeMarkersFromOverlay();
						removeObjectAssociatedMarkerForML(3);
						train(3);
					}
					else if(e.getSource() == objectAssociatedMarker4SaveButton){
						updateAnnotateChannelPatternButtons(22);
						saveDataForLogisticRegression(3);
					}
					else if(e.getSource() == objectAssociatedMarker4LoadButton){
						updateAnnotateChannelPatternButtons(22);
						loadDataForLogisticRegression(3);
					}
					else if(e.getSource() == objectAssociatedMarker5TrainButton){
						if(currentObjectAssociatedMarker!=4){
							updateAnnotateChannelPatternButtons(28);
						}
						removeMarkersFromOverlay();
						removeObjectAssociatedMarkerForML(4);
						train(4);
					}
					else if(e.getSource() == objectAssociatedMarker5SaveButton){
						updateAnnotateChannelPatternButtons(28);
						saveDataForLogisticRegression(4);
					}
					else if(e.getSource() == objectAssociatedMarker5LoadButton){
						updateAnnotateChannelPatternButtons(28);
						loadDataForLogisticRegression(4);
					}
					else if(e.getSource() == objectAssociatedMarker6TrainButton){
						if(currentObjectAssociatedMarker!=5){
							updateAnnotateChannelPatternButtons(34);
						}
						removeMarkersFromOverlay();
						removeObjectAssociatedMarkerForML(5);
						train(5);
					}
					else if(e.getSource() == objectAssociatedMarker6SaveButton){
						updateAnnotateChannelPatternButtons(34);
						saveDataForLogisticRegression(5);
					}
					else if(e.getSource() == objectAssociatedMarker6LoadButton){
						updateAnnotateChannelPatternButtons(34);
						loadDataForLogisticRegression(5);
					}
					else if(e.getSource() == objectAssociatedMarker7TrainButton){
						if(currentObjectAssociatedMarker!=6){
							updateAnnotateChannelPatternButtons(40);
						}
						removeMarkersFromOverlay();
						removeObjectAssociatedMarkerForML(6);
						train(6);
					}
					else if(e.getSource() == objectAssociatedMarker7SaveButton){
						updateAnnotateChannelPatternButtons(40);
						saveDataForLogisticRegression(6);
					}
					else if(e.getSource() == objectAssociatedMarker7LoadButton){
						updateAnnotateChannelPatternButtons(40);
						loadDataForLogisticRegression(6);
					}
					else if(e.getSource() == analyzeMarkersButton){
						markerMeasurements();
					}
					else if(e.getSource() == markerSnapshotButton){
						takeMarkerSnapshot();
					}
					else if(e.getSource() == loadSegmentationButton){
						loadNucleiSegmentations();
					}
					else if(e.getSource() == saveSegmentationButton){
						saveNucleiSegmentation();
					}
					else if(e.getSource() == loadObjectAssociatedMarkerButton){
						loadObjectAssociatedMarkerIdentifications();
					}
					else if(e.getSource() == saveObjectAssociatedMarkerButton){
						saveObjectAssociatedMarkerIdentifications();
					}
					else if(e.getSource() == loadAreaButton){
						loadAreas();
					}
					else if(e.getSource() == saveAreaButton){
						saveAreas();
					}
					else if(e.getSource() == loadImageAndSegmentationButton){
						loadNucleiAndSegmentation();
					}
				}							
			});
		}
	};

	protected class RoiListener implements MouseListener
	{
		@Override
		public void mouseClicked(MouseEvent e) {}

		@Override
		public void mouseEntered(MouseEvent e) {}

		@Override
		public void mouseExited(MouseEvent e) {}

		@Override
		public void mousePressed(MouseEvent e) {
			if(e.getButton() == MouseEvent.BUTTON3){
				if(mousePanning){
					mousePanning = false;
					if(currentMode==0) {
						if(newObjectButton.isSelected()) {
							Toolbar.getInstance().setTool(Toolbar.FREEROI);}
						else if(removeObjectButton.isSelected()||mergeObjectsButton.isSelected()||swapObjectClassButton.isSelected()) {
							Toolbar.getInstance().setTool(Toolbar.POINT);}
						else if(splitObjectsButton.isSelected()) {
							Toolbar.getInstance().setTool(Toolbar.FREELINE);}
					}
					else {Toolbar.getInstance().setTool(Toolbar.POINT);}
				}
			}
		}

		@Override
		public void mouseReleased( final MouseEvent e )
		{
			if(SwingUtilities.isLeftMouseButton(e)){
				
				double current_click_time = System.currentTimeMillis();
				if((current_click_time-previous_click_time)<500){
					IJ.run("Select None");
				}
				previous_click_time = current_click_time;
				if(!mousePanning) {
					Roi roi = displayImage.getRoi();
					if (roi != null && roi.getType() == Roi.FREEROI && currentMode == 0) {
						if(newObjectButton.isSelected()) {
							if(objectDisplayFlag){addObject();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the objects to be able to process them.");}
						}
						if(newAreaButton.isSelected()) {
							if(areaDisplayFlag){addArea();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the areas to be able to process them.");}
						}
					}
					if (roi != null && roi.getType() == Roi.POINT && currentMode == 0) {
						if(mergeObjectsButton.isSelected()) {
							if(objectDisplayFlag){mergeObjects();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the objects to be able to process them.");}
						}
						if(removeObjectButton.isSelected()) {
							if(objectDisplayFlag){removeObject();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the objects to be able to process them.");}
						}
						if(swapObjectClassButton.isSelected()) {
							if(objectDisplayFlag){swapObjectClass();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the objects to be able to process them.");}
						}
						if(removeAreaButton.isSelected()) {
							if(areaDisplayFlag){removeArea();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the areas to be able to process them.");}
						}
						if(swapAreaClassButton.isSelected()) {
							if(areaDisplayFlag){swapAreaClass();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the areas to be able to process them.");}
						}
					}
					if (roi != null && roi.getType() == Roi.POINT && currentMode == 1) {
						if(currentObjectAssociatedMarker>(-1)){
							if(methodToIdentifyObjectAssociatedMarkers[currentObjectAssociatedMarker]<2){
								if(objectDisplayFlag){annotateNucleusMarker();}
								else{
									Roi r = displayImage.getRoi();
									if (null == r){
										return;
									}
									displayImage.killRoi();
									IJ.showMessage("You need to visualize the objects to be able to annotate them.");}
							}
							else{
								if(objectDisplayFlag){labelNucleusMarker();}
								else{
									Roi r = displayImage.getRoi();
									if (null == r){
										return;
									}
									displayImage.killRoi();
									IJ.showMessage("You need to visualize the objects to be able to label them.");}
							}
						}
					}
					if (roi != null && roi.getType() == Roi.FREELINE && currentMode == 0) {
						if(splitObjectsButton.isSelected()) {
							if(objectDisplayFlag){splitObject();}
							else{
								Roi r = displayImage.getRoi();
								if (null == r){
									return;
								}
								displayImage.killRoi();
								IJ.showMessage("You need to visualize the objects to be able to process them.");}
						}
					}
				}
			}
		}

	}

	public void navigateUp(ImagePlus imp) {
		int height = imp.getHeight();
		Rectangle srcRect = imp.getCanvas().getSrcRect();
		int xstart = srcRect.x;
		int ystart = srcRect.y;
		srcRect.y -= Math.max(height/200, 1);
		if (srcRect.y<0) srcRect.y = 0;
		//if (srcRect.y+srcRect.height>height) srcRect.y =
		//		height-srcRect.height;
		if (srcRect.x!=xstart || srcRect.y!=ystart)
			displayImage.getCanvas().repaint();
	}

	public void navigateDown(ImagePlus imp) {
		int height = imp.getHeight();
		Rectangle srcRect = imp.getCanvas().getSrcRect();
		int xstart = srcRect.x;
		int ystart = srcRect.y;
		srcRect.y += Math.max(height/200, 1);
		//if (srcRect.y<0) srcRect.y = 0;
		if (srcRect.y+srcRect.height>height) srcRect.y = height-srcRect.height;
		if (srcRect.x!=xstart || srcRect.y!=ystart)
			displayImage.getCanvas().repaint();
	}

	public void navigateLeft(ImagePlus imp) {
		int width = imp.getWidth();
		Rectangle srcRect = imp.getCanvas().getSrcRect();
		int xstart = srcRect.x;
		int ystart = srcRect.y;
		srcRect.x -= Math.max(width/200, 1);
		if (srcRect.x<0) srcRect.x = 0;
		if (srcRect.x!=xstart || srcRect.y!=ystart)
			displayImage.getCanvas().repaint();
	}

	public void navigateRight(ImagePlus imp) {
		int width = imp.getWidth();
		Rectangle srcRect = imp.getCanvas().getSrcRect();
		int xstart = srcRect.x;
		int ystart = srcRect.y;
		srcRect.x += Math.max(width/200, 1);
		if (srcRect.x+srcRect.width>width) srcRect.x = width-srcRect.width;
		if (srcRect.x!=xstart || srcRect.y!=ystart)
			displayImage.getCanvas().repaint();
	}

	protected class	KeyActions implements KeyListener
	{
		@Override
		public void keyTyped(KeyEvent e) {
		}

		@Override
		public void keyReleased(KeyEvent e) {
			switch (e.getKeyCode()) {
			case KeyEvent.VK_SPACE:
				mousePanning = false;
				if(currentMode==0) {
					if(newObjectButton.isSelected()) {
						Toolbar.getInstance().setTool(Toolbar.FREEROI);}
					else if(removeObjectButton.isSelected()||mergeObjectsButton.isSelected()||swapObjectClassButton.isSelected()) {
						Toolbar.getInstance().setTool(Toolbar.POINT);}
					else if(splitObjectsButton.isSelected()) {
						Toolbar.getInstance().setTool(Toolbar.FREELINE);}
				}
				else {Toolbar.getInstance().setTool(Toolbar.POINT);}
				break;
			}
		}

		@Override
		public void keyPressed(KeyEvent e) {
			switch (e.getKeyCode()) {
			case KeyEvent.VK_SPACE:
				if(!mousePanning) {mousePanning = true;Toolbar.getInstance().setTool(Toolbar.HAND);}
				break;

			case KeyEvent.VK_LEFT:
				navigateLeft(displayImage);
				break;

			case KeyEvent.VK_UP:
				navigateUp(displayImage);
				break;

			case KeyEvent.VK_RIGHT:
				navigateRight(displayImage);
				break;

			case KeyEvent.VK_DOWN:
				navigateDown(displayImage);
				break;
			case KeyEvent.VK_KP_LEFT:
				navigateLeft(displayImage);
				break;

			case KeyEvent.VK_KP_UP:
				navigateUp(displayImage);
				break;

			case KeyEvent.VK_KP_RIGHT:
				navigateRight(displayImage);
				break;

			case KeyEvent.VK_KP_DOWN:
				navigateDown(displayImage);
				break;
				

			case KeyEvent.VK_ADD:
				IJ.run("In [+]");
				break;

			case KeyEvent.VK_SUBTRACT:
				IJ.run("Out [-]");
				break;

			case KeyEvent.VK_EQUALS:
				IJ.run("In [+]");
				break;

			case KeyEvent.VK_MINUS:
				IJ.run("Out [-]");
				break;

			default:
				break;
			}
		}
	};

	// get ROI coordinates
	void showCoordinates(FreehandRoi roi) {
		Rectangle r = roi!=null?roi.getBounds():new Rectangle(0,0,displayImage.getWidth(),displayImage.getHeight());
		ImageProcessor mask = roi!=null?roi.getMask():null;
		for (int y=0; y<r.height; y++) {
			for (int x=0; x<r.width; x++) {
				if (mask==null||mask.getPixel(x,y)!=0) {
					IJ.log((x+r.x) + "," + (y+r.y));
				}
			}
		}
	}
	/**
	 * Custom canvas to deal with zooming and panning
	 */
	private class CustomCanvas extends OverlayedImageCanvas 
	{
		CustomCanvas(ImagePlus imp) 
		{
			super(imp);
			Dimension dim = new Dimension(Math.min(512, imp.getWidth()), Math.min(512, imp.getHeight()));
			setMinimumSize(dim);
			setSize(dim.width, dim.height);
			setDstDimensions(dim.width, dim.height);
			addKeyListener(new KeyAdapter() {
				public void keyReleased(KeyEvent ke) {
					repaint();
				}
			});
			// remove key actions that normally come with ImageJ
			// so we can define the keys that are useful for the plugin
			for (KeyListener l : getKeyListeners()) {
				removeKeyListener(l);
			}
		}
		//@Override
		public void setDrawingSize(int w, int h) {}

		public void setDstDimensions(int width, int height) {
			super.dstWidth = width;
			super.dstHeight = height;
			// adjust srcRect: can it grow/shrink?
			int w = Math.min((int)(width  / magnification), imp.getWidth());
			int h = Math.min((int)(height / magnification), imp.getHeight());
			int x = srcRect.x;
			if (x + w > imp.getWidth()) x = w - imp.getWidth();
			int y = srcRect.y;
			if (y + h > imp.getHeight()) y = h - imp.getHeight();
			srcRect.setRect(x, y, w, h);
			repaint();
		}

		//@Override
		public void paint(Graphics g) {
			
			Rectangle srcRect = getSrcRect();
			double mag = getMagnification();
			int dw = (int)(srcRect.width * mag);
			int dh = (int)(srcRect.height * mag);
			g.setClip(0, 0, dw, dh);

			super.paint(g);

			int w = getWidth();
			int h = getHeight();
			g.setClip(0, 0, w, h);

			// Paint away the outside
			g.setColor(getBackground());
			g.fillRect(dw, 0, w - dw, h);
			g.fillRect(0, dh, w, h - dh);
		}

	}

	/**
	 * Functions to remove marker associated buttons
	 */
	public void removeMarker1ButtonFromListener() {
		objectAssociatedMarker1Button.removeActionListener(listener);
		objectAssociatedMarker1ColorButton.removeActionListener(listener);
		objectAssociatedMarker1ColorMLButton.removeActionListener(listener);
		objectAssociatedMarker1RemoveButton.removeActionListener(listener);
		objectAssociatedMarker1PositiveLabelButton.removeActionListener(listener);
		objectAssociatedMarker1NegativeLabelButton.removeActionListener(listener);
		objectAssociatedMarker1TrainButton.removeActionListener(listener);
		objectAssociatedMarker1LoadButton.removeActionListener(listener);
		objectAssociatedMarker1SaveButton.removeActionListener(listener);
		objectAssociatedMarker1Pattern1Button.removeActionListener(listener);
		objectAssociatedMarker1Pattern2Button.removeActionListener(listener);
		objectAssociatedMarker1Pattern3Button.removeActionListener(listener);
		objectAssociatedMarker1Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker2ButtonFromListener() {
		objectAssociatedMarker2Button.removeActionListener(listener);
		objectAssociatedMarker2ColorButton.removeActionListener(listener);
		objectAssociatedMarker2ColorMLButton.removeActionListener(listener);
		objectAssociatedMarker2RemoveButton.removeActionListener(listener);
		objectAssociatedMarker2PositiveLabelButton.removeActionListener(listener);
		objectAssociatedMarker2NegativeLabelButton.removeActionListener(listener);
		objectAssociatedMarker2TrainButton.removeActionListener(listener);
		objectAssociatedMarker2LoadButton.removeActionListener(listener);
		objectAssociatedMarker2SaveButton.removeActionListener(listener);
		objectAssociatedMarker2Pattern1Button.removeActionListener(listener);
		objectAssociatedMarker2Pattern2Button.removeActionListener(listener);
		objectAssociatedMarker2Pattern3Button.removeActionListener(listener);
		objectAssociatedMarker2Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker3ButtonFromListener() {
		objectAssociatedMarker3Button.removeActionListener(listener);
		objectAssociatedMarker3ColorButton.removeActionListener(listener);
		objectAssociatedMarker3ColorMLButton.removeActionListener(listener);
		objectAssociatedMarker3RemoveButton.removeActionListener(listener);
		objectAssociatedMarker3PositiveLabelButton.removeActionListener(listener);
		objectAssociatedMarker3NegativeLabelButton.removeActionListener(listener);
		objectAssociatedMarker3TrainButton.removeActionListener(listener);
		objectAssociatedMarker3LoadButton.removeActionListener(listener);
		objectAssociatedMarker3SaveButton.removeActionListener(listener);
		objectAssociatedMarker3Pattern1Button.removeActionListener(listener);
		objectAssociatedMarker3Pattern2Button.removeActionListener(listener);
		objectAssociatedMarker3Pattern3Button.removeActionListener(listener);
		objectAssociatedMarker3Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker4ButtonFromListener() {
		objectAssociatedMarker4Button.removeActionListener(listener);
		objectAssociatedMarker4ColorButton.removeActionListener(listener);
		objectAssociatedMarker4ColorMLButton.removeActionListener(listener);
		objectAssociatedMarker4RemoveButton.removeActionListener(listener);
		objectAssociatedMarker4PositiveLabelButton.removeActionListener(listener);
		objectAssociatedMarker4NegativeLabelButton.removeActionListener(listener);
		objectAssociatedMarker4TrainButton.removeActionListener(listener);
		objectAssociatedMarker4LoadButton.removeActionListener(listener);
		objectAssociatedMarker4SaveButton.removeActionListener(listener);
		objectAssociatedMarker4Pattern1Button.removeActionListener(listener);
		objectAssociatedMarker4Pattern2Button.removeActionListener(listener);
		objectAssociatedMarker4Pattern3Button.removeActionListener(listener);
		objectAssociatedMarker4Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker5ButtonFromListener() {
		objectAssociatedMarker5Button.removeActionListener(listener);
		objectAssociatedMarker5ColorButton.removeActionListener(listener);
		objectAssociatedMarker5ColorMLButton.removeActionListener(listener);
		objectAssociatedMarker5RemoveButton.removeActionListener(listener);
		objectAssociatedMarker5PositiveLabelButton.removeActionListener(listener);
		objectAssociatedMarker5NegativeLabelButton.removeActionListener(listener);
		objectAssociatedMarker5TrainButton.removeActionListener(listener);
		objectAssociatedMarker5LoadButton.removeActionListener(listener);
		objectAssociatedMarker5SaveButton.removeActionListener(listener);
		objectAssociatedMarker5Pattern1Button.removeActionListener(listener);
		objectAssociatedMarker5Pattern2Button.removeActionListener(listener);
		objectAssociatedMarker5Pattern3Button.removeActionListener(listener);
		objectAssociatedMarker5Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker6ButtonFromListener() {
		objectAssociatedMarker6Button.removeActionListener(listener);
		objectAssociatedMarker6ColorButton.removeActionListener(listener);
		objectAssociatedMarker6ColorMLButton.removeActionListener(listener);
		objectAssociatedMarker6RemoveButton.removeActionListener(listener);
		objectAssociatedMarker6PositiveLabelButton.removeActionListener(listener);
		objectAssociatedMarker6NegativeLabelButton.removeActionListener(listener);
		objectAssociatedMarker6TrainButton.removeActionListener(listener);
		objectAssociatedMarker6LoadButton.removeActionListener(listener);
		objectAssociatedMarker6SaveButton.removeActionListener(listener);
		objectAssociatedMarker6Pattern1Button.removeActionListener(listener);
		objectAssociatedMarker6Pattern2Button.removeActionListener(listener);
		objectAssociatedMarker6Pattern3Button.removeActionListener(listener);
		objectAssociatedMarker6Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker7ButtonFromListener() {
		objectAssociatedMarker7Button.removeActionListener(listener);
		objectAssociatedMarker7ColorButton.removeActionListener(listener);
		objectAssociatedMarker7ColorMLButton.removeActionListener(listener);
		objectAssociatedMarker7RemoveButton.removeActionListener(listener);
		objectAssociatedMarker7PositiveLabelButton.removeActionListener(listener);
		objectAssociatedMarker7NegativeLabelButton.removeActionListener(listener);
		objectAssociatedMarker7TrainButton.removeActionListener(listener);
		objectAssociatedMarker7LoadButton.removeActionListener(listener);
		objectAssociatedMarker7SaveButton.removeActionListener(listener);
		objectAssociatedMarker7Pattern1Button.removeActionListener(listener);
		objectAssociatedMarker7Pattern2Button.removeActionListener(listener);
		objectAssociatedMarker7Pattern3Button.removeActionListener(listener);
		objectAssociatedMarker7Pattern4Button.removeActionListener(listener);
	}
	/**
	 * Functions to remove marker associated buttons
	 */
	public void addMarker1ButtonFromListener() {
		objectAssociatedMarker1Button.addActionListener(listener);
		objectAssociatedMarker1ColorButton.addActionListener(listener);
		objectAssociatedMarker1ColorMLButton.addActionListener(listener);
		objectAssociatedMarker1RemoveButton.addActionListener(listener);
		objectAssociatedMarker1PositiveLabelButton.addActionListener(listener);
		objectAssociatedMarker1NegativeLabelButton.addActionListener(listener);
		objectAssociatedMarker1TrainButton.addActionListener(listener);
		objectAssociatedMarker1LoadButton.addActionListener(listener);
		objectAssociatedMarker1SaveButton.addActionListener(listener);
		objectAssociatedMarker1Pattern1Button.addActionListener(listener);
		objectAssociatedMarker1Pattern2Button.addActionListener(listener);
		objectAssociatedMarker1Pattern3Button.addActionListener(listener);
		objectAssociatedMarker1Pattern4Button.addActionListener(listener);
	}
	public void addMarker2ButtonFromListener() {
		objectAssociatedMarker2Button.addActionListener(listener);
		objectAssociatedMarker2ColorButton.addActionListener(listener);
		objectAssociatedMarker2ColorMLButton.addActionListener(listener);
		objectAssociatedMarker2RemoveButton.addActionListener(listener);
		objectAssociatedMarker2PositiveLabelButton.addActionListener(listener);
		objectAssociatedMarker2NegativeLabelButton.addActionListener(listener);
		objectAssociatedMarker2TrainButton.addActionListener(listener);
		objectAssociatedMarker2LoadButton.addActionListener(listener);
		objectAssociatedMarker2SaveButton.addActionListener(listener);
		objectAssociatedMarker2Pattern1Button.addActionListener(listener);
		objectAssociatedMarker2Pattern2Button.addActionListener(listener);
		objectAssociatedMarker2Pattern3Button.addActionListener(listener);
		objectAssociatedMarker2Pattern4Button.addActionListener(listener);
	}
	public void addMarker3ButtonFromListener() {
		objectAssociatedMarker3Button.addActionListener(listener);
		objectAssociatedMarker3ColorButton.addActionListener(listener);
		objectAssociatedMarker3ColorMLButton.addActionListener(listener);
		objectAssociatedMarker3RemoveButton.addActionListener(listener);
		objectAssociatedMarker3PositiveLabelButton.addActionListener(listener);
		objectAssociatedMarker3NegativeLabelButton.addActionListener(listener);
		objectAssociatedMarker3TrainButton.addActionListener(listener);
		objectAssociatedMarker3LoadButton.addActionListener(listener);
		objectAssociatedMarker3SaveButton.addActionListener(listener);
		objectAssociatedMarker3Pattern1Button.addActionListener(listener);
		objectAssociatedMarker3Pattern2Button.addActionListener(listener);
		objectAssociatedMarker3Pattern3Button.addActionListener(listener);
		objectAssociatedMarker3Pattern4Button.addActionListener(listener);
	}
	public void addMarker4ButtonFromListener() {
		objectAssociatedMarker4Button.addActionListener(listener);
		objectAssociatedMarker4ColorButton.addActionListener(listener);
		objectAssociatedMarker4ColorMLButton.addActionListener(listener);
		objectAssociatedMarker4RemoveButton.addActionListener(listener);
		objectAssociatedMarker4PositiveLabelButton.addActionListener(listener);
		objectAssociatedMarker4NegativeLabelButton.addActionListener(listener);
		objectAssociatedMarker4TrainButton.addActionListener(listener);
		objectAssociatedMarker4LoadButton.addActionListener(listener);
		objectAssociatedMarker4SaveButton.addActionListener(listener);
		objectAssociatedMarker4Pattern1Button.addActionListener(listener);
		objectAssociatedMarker4Pattern2Button.addActionListener(listener);
		objectAssociatedMarker4Pattern3Button.addActionListener(listener);
		objectAssociatedMarker4Pattern4Button.addActionListener(listener);
	}
	public void addMarker5ButtonFromListener() {
		objectAssociatedMarker5Button.addActionListener(listener);
		objectAssociatedMarker5ColorButton.addActionListener(listener);
		objectAssociatedMarker5ColorMLButton.addActionListener(listener);
		objectAssociatedMarker5RemoveButton.addActionListener(listener);
		objectAssociatedMarker5PositiveLabelButton.addActionListener(listener);
		objectAssociatedMarker5NegativeLabelButton.addActionListener(listener);
		objectAssociatedMarker5TrainButton.addActionListener(listener);
		objectAssociatedMarker5LoadButton.addActionListener(listener);
		objectAssociatedMarker5SaveButton.addActionListener(listener);
		objectAssociatedMarker5Pattern1Button.addActionListener(listener);
		objectAssociatedMarker5Pattern2Button.addActionListener(listener);
		objectAssociatedMarker5Pattern3Button.addActionListener(listener);
		objectAssociatedMarker5Pattern4Button.addActionListener(listener);
	}
	public void addMarker6ButtonFromListener() {
		objectAssociatedMarker6Button.addActionListener(listener);
		objectAssociatedMarker6ColorButton.addActionListener(listener);
		objectAssociatedMarker6ColorMLButton.addActionListener(listener);
		objectAssociatedMarker6RemoveButton.addActionListener(listener);
		objectAssociatedMarker6PositiveLabelButton.addActionListener(listener);
		objectAssociatedMarker6NegativeLabelButton.addActionListener(listener);
		objectAssociatedMarker6TrainButton.addActionListener(listener);
		objectAssociatedMarker6LoadButton.addActionListener(listener);
		objectAssociatedMarker6SaveButton.addActionListener(listener);
		objectAssociatedMarker6Pattern1Button.addActionListener(listener);
		objectAssociatedMarker6Pattern2Button.addActionListener(listener);
		objectAssociatedMarker6Pattern3Button.addActionListener(listener);
		objectAssociatedMarker6Pattern4Button.addActionListener(listener);
	}
	public void addMarker7ButtonFromListener() {
		objectAssociatedMarker7Button.addActionListener(listener);
		objectAssociatedMarker7ColorButton.addActionListener(listener);
		objectAssociatedMarker7ColorMLButton.addActionListener(listener);
		objectAssociatedMarker7RemoveButton.addActionListener(listener);
		objectAssociatedMarker7PositiveLabelButton.addActionListener(listener);
		objectAssociatedMarker7NegativeLabelButton.addActionListener(listener);
		objectAssociatedMarker7TrainButton.addActionListener(listener);
		objectAssociatedMarker7LoadButton.addActionListener(listener);
		objectAssociatedMarker7SaveButton.addActionListener(listener);
		objectAssociatedMarker7Pattern1Button.addActionListener(listener);
		objectAssociatedMarker7Pattern2Button.addActionListener(listener);
		objectAssociatedMarker7Pattern3Button.addActionListener(listener);
		objectAssociatedMarker7Pattern4Button.addActionListener(listener);
	}
	/**
	 * Change font for Swing components to adopt current GUI scale
	 */
	void scale(JRadioButton button){
		if(Prefs.getGuiScale()!=1.0){
			button.setFont(button.getFont().deriveFont((float)(button.getFont().getSize()*Prefs.getGuiScale())));
		}
	}
	void scale(JButton button){
		if(Prefs.getGuiScale()!=1.0){
			button.setFont(button.getFont().deriveFont((float)(button.getFont().getSize()*Prefs.getGuiScale())));
		}
	}
	void scale(JSlider slider){
		if(Prefs.getGuiScale()!=1.0){
			slider.setFont(slider.getFont().deriveFont((float)(slider.getFont().getSize()*Prefs.getGuiScale())));
		}
	}
	void scale(JTextArea text_area){
		if(Prefs.getGuiScale()!=1.0){
			text_area.setFont(text_area.getFont().deriveFont((float)(text_area.getFont().getSize()*Prefs.getGuiScale())));
		}
	}
	void scale(JLabel JL){
		if(Prefs.getGuiScale()!=1.0){
			JL.setFont(JL.getFont().deriveFont((float)(JL.getFont().getSize()*Prefs.getGuiScale())));
		}
	}
	/**
	 * Custom window to define the GUI
	 */
	private class CustomWindow extends ImageWindow 
	{
		
		private JPanel modePanel = new JPanel();
		private JPanel analysisPanel1 = new JPanel();
		private JPanel analysisPanel2 = new JPanel();
		private JPanel annotationPanel1 = new JPanel();
		private JPanel classesPanel = new JPanel();
		private JPanel class1Panel = new JPanel();
		private JPanel class2Panel = new JPanel();
		private JPanel class3Panel = new JPanel();
		private JPanel class4Panel = new JPanel();
		private JPanel class5Panel = new JPanel();
		private JPanel annotationPanel2 = new JPanel();
		private JPanel areaPanel = new JPanel();
		private JPanel area1Panel = new JPanel();
		private JPanel area2Panel = new JPanel();
		private JPanel area3Panel = new JPanel();
		private JPanel area4Panel = new JPanel();
		private JPanel area5Panel = new JPanel();
		private JPanel loadImageAndSegmentationPanel = new JPanel();
		private JPanel objectAssociatedMarkersPanel = new JPanel();
		private JPanel marker1PatternPanel1 = new JPanel();
		private JPanel marker1PatternPanel2 = new JPanel();
		private JPanel marker1PatternPanel3 = new JPanel();
		private JPanel marker2PatternPanel1 = new JPanel();
		private JPanel marker2PatternPanel2 = new JPanel();
		private JPanel marker2PatternPanel3 = new JPanel();
		private JPanel marker3PatternPanel1 = new JPanel();
		private JPanel marker3PatternPanel2 = new JPanel();
		private JPanel marker3PatternPanel3 = new JPanel();
		private JPanel marker4PatternPanel1 = new JPanel();
		private JPanel marker4PatternPanel2 = new JPanel();
		private JPanel marker4PatternPanel3 = new JPanel();
		private JPanel marker5PatternPanel1 = new JPanel();
		private JPanel marker5PatternPanel2 = new JPanel();
		private JPanel marker5PatternPanel3 = new JPanel();
		private JPanel marker6PatternPanel1 = new JPanel();
		private JPanel marker6PatternPanel2 = new JPanel();
		private JPanel marker6PatternPanel3 = new JPanel();
		private JPanel marker7PatternPanel1 = new JPanel();
		private JPanel marker7PatternPanel2 = new JPanel();
		private JPanel marker7PatternPanel3 = new JPanel();
		private JPanel visualizationPanel1 = new JPanel();
		private JPanel visualizationPanel2 = new JPanel();
		private JPanel visualizationPanel3 = new JPanel();
		private JPanel visualizationPanel4 = new JPanel();
		private JPanel filePanel1 = new JPanel();
		private JPanel filePanel2 = new JPanel();
		private JPanel filePanel3 = new JPanel();

		private JPanel topPanel = new JPanel();
		private JPanel leftPanel1 = new JPanel();
		private JPanel rightPanel1 = new JPanel();
		private JPanel leftPanel2 = new JPanel();
		private JPanel rightPanel2 = new JPanel();
		private JPanel bottomPanel1 = new JPanel();

		private Panel all = new Panel();
		
		GridBagLayout classesLayout = new GridBagLayout();
		GridBagConstraints classesConstraints = new GridBagConstraints();
		GridBagLayout areaLayout = new GridBagLayout();
		GridBagConstraints areaConstraints = new GridBagConstraints();
		GridBagLayout loadImageAndSegmentationLayout = new GridBagLayout();
		GridBagConstraints loadImageAndSegmentationConstraints = new GridBagConstraints();
		GridBagLayout objectAssociatedMarkersLayout = new GridBagLayout();
		GridBagConstraints objectAssociatedMarkersConstraints = new GridBagConstraints();
		GridBagLayout analysisLayout1 = new GridBagLayout();
		GridBagConstraints analysisConstraints1 = new GridBagConstraints();

		CustomWindow(ImagePlus imp) 
		{
			super(imp, new CustomCanvas(imp));

			final CustomCanvas canvas = (CustomCanvas) getCanvas();

			// Remove the canvas from the window, to add it later
			removeAll();

			setTitle("Annotater");

			// Mode panel
			GridBagLayout modeLayout = new GridBagLayout();
			GridBagConstraints modeConstraints = new GridBagConstraints();
			modeConstraints.anchor = GridBagConstraints.NORTHWEST;
			modeConstraints.fill = GridBagConstraints.HORIZONTAL;
			modeConstraints.gridwidth = 1;
			modeConstraints.gridheight = 1;
			modeConstraints.gridx = 0;
			modeConstraints.gridy = 0;
			modePanel.setLayout(modeLayout);

			if(Prefs.getGuiScale()==1.0){
				modePanel.setBorder(BorderFactory.createTitledBorder("Mode"));
			}
			else{
				JTextArea modeTitle = new JTextArea("Mode");
				scale(modeTitle);
				modePanel.add(modeTitle, modeConstraints);
				modeConstraints.gridx++;
				JTextArea blankTitle = new JTextArea("");
				scale(blankTitle);
				modePanel.add(blankTitle, modeConstraints);
				modeConstraints.gridy++;
				modeConstraints.gridx=0;
			}
			modePanel.add(objectsAnnotationButton,modeConstraints);
			modeConstraints.gridx++;
			modePanel.add(markerAnnotationButton,modeConstraints);
			modeConstraints.gridx++;
			if(currentMode==0) {
				objectsAnnotationButton.setSelected(true);
				markerAnnotationButton.setSelected(false);
			}
			else {
				objectsAnnotationButton.setSelected(false);
				markerAnnotationButton.setSelected(true);
			}


			// File panel 1
			filePanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout fileLayout1 = new GridBagLayout();
			GridBagConstraints fileConstraints1 = new GridBagConstraints();
			fileConstraints1.anchor = GridBagConstraints.NORTHWEST;
			fileConstraints1.fill = GridBagConstraints.HORIZONTAL;
			fileConstraints1.gridwidth = 1;
			fileConstraints1.gridheight = 1;
			fileConstraints1.gridx = 0;
			fileConstraints1.gridy = 0;
			filePanel1.setLayout(fileLayout1);

			filePanel1.add(loadSegmentationButton);
			fileConstraints1.gridx++;
			filePanel1.add(saveSegmentationButton);

			// File panel 2
			filePanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout fileLayout2 = new GridBagLayout();
			GridBagConstraints fileConstraints2 = new GridBagConstraints();
			fileConstraints2.anchor = GridBagConstraints.NORTHWEST;
			fileConstraints2.fill = GridBagConstraints.HORIZONTAL;
			fileConstraints2.gridwidth = 1;
			fileConstraints2.gridheight = 1;
			fileConstraints2.gridx = 0;
			fileConstraints2.gridy = 0;
			filePanel2.setLayout(fileLayout2);

			filePanel2.add(loadObjectAssociatedMarkerButton,fileConstraints2);
			fileConstraints2.gridx++;
			filePanel2.add(saveObjectAssociatedMarkerButton,fileConstraints2);
			fileConstraints2.gridx++;

			// File panel 3
			filePanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout fileLayout3 = new GridBagLayout();
			GridBagConstraints fileConstraints3 = new GridBagConstraints();
			fileConstraints3.anchor = GridBagConstraints.NORTHWEST;
			fileConstraints3.fill = GridBagConstraints.HORIZONTAL;
			fileConstraints3.gridwidth = 1;
			fileConstraints3.gridheight = 1;
			fileConstraints3.gridx = 0;
			fileConstraints3.gridy = 0;
			filePanel3.setLayout(fileLayout3);

			filePanel3.add(loadAreaButton,fileConstraints3);
			fileConstraints3.gridx++;
			filePanel3.add(saveAreaButton,fileConstraints3);
			fileConstraints3.gridx++;

			// Analysis panel 1
			analysisConstraints1.anchor = GridBagConstraints.NORTHWEST;
			analysisConstraints1.fill = GridBagConstraints.HORIZONTAL;
			analysisConstraints1.gridwidth = 1;
			analysisConstraints1.gridheight = 1;
			analysisConstraints1.gridx = 0;
			analysisConstraints1.gridy = 0;
			analysisPanel1.setLayout(analysisLayout1);

			if(Prefs.getGuiScale()==1.0){
				analysisPanel1.setBorder(BorderFactory.createTitledBorder("Analysis"));
			}
			else{
				JTextArea analysisPanel1Title = new JTextArea("Analysis");
				scale(analysisPanel1Title);
				analysisPanel1.add(analysisPanel1Title, analysisConstraints1);
				analysisConstraints1.gridy++;
			}
			analysisPanel1.add(analyzeClassesButton,analysisConstraints1);
			analysisConstraints1.gridy++;
			analysisPanel1.add(classSnapshotButton,analysisConstraints1);
			analysisConstraints1.gridy++;
			analysisPanel1.add(batchClassesMeasurementsButton,analysisConstraints1);

			// Analysis panel 2
			GridBagLayout analysisLayout2 = new GridBagLayout();
			GridBagConstraints analysisConstraints2 = new GridBagConstraints();
			analysisConstraints2.anchor = GridBagConstraints.NORTHWEST;
			analysisConstraints2.fill = GridBagConstraints.HORIZONTAL;
			analysisConstraints2.gridwidth = 1;
			analysisConstraints2.gridheight = 1;
			analysisConstraints2.gridx = 0;
			analysisConstraints2.gridy = 0;
			analysisPanel2.setLayout(analysisLayout2);

			if(Prefs.getGuiScale()==1.0){
				analysisPanel2.setBorder(BorderFactory.createTitledBorder("Analysis"));
			}
			else{
				JTextArea analysisPanel2Title = new JTextArea("Analysis");
				scale(analysisPanel2Title);
				analysisPanel2.add(analysisPanel2Title, analysisConstraints2);
				analysisConstraints2.gridy++;
			}
			analysisPanel2.add(analyzeMarkersButton, analysisConstraints2);
			analysisConstraints2.gridy++;
			analysisPanel2.add(markerSnapshotButton,analysisConstraints2);
			analysisConstraints2.gridy++;
			analysisPanel2.add(batchMarkersButton, analysisConstraints2);
			analysisConstraints2.gridy++;

			// Marker 1 pattern panel
			marker1PatternPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker1PatternLayout1 = new GridBagLayout();
			GridBagConstraints marker1PatternConstraints1 = new GridBagConstraints();
			marker1PatternConstraints1.anchor = GridBagConstraints.NORTHWEST;
			marker1PatternConstraints1.fill = GridBagConstraints.HORIZONTAL;
			marker1PatternConstraints1.gridwidth = 1;
			marker1PatternConstraints1.gridheight = 1;
			marker1PatternConstraints1.gridx = 0;
			marker1PatternConstraints1.gridy = 0;
			marker1PatternPanel1.setLayout(marker1PatternLayout1);
			marker1PatternPanel1.add(objectAssociatedMarker1Button);
			marker1PatternConstraints1.gridx++;
			marker1PatternPanel1.add(objectAssociatedMarker1ColorButton);
			marker1PatternConstraints1.gridx++;
			marker1PatternPanel1.add(objectAssociatedMarker1RemoveButton);

			marker1PatternPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker1PatternLayout2 = new GridBagLayout();
			GridBagConstraints marker1PatternConstraints2 = new GridBagConstraints();
			marker1PatternConstraints2.anchor = GridBagConstraints.NORTHWEST;
			marker1PatternConstraints2.fill = GridBagConstraints.HORIZONTAL;
			marker1PatternConstraints2.gridwidth = 1;
			marker1PatternConstraints2.gridheight = 1;
			marker1PatternConstraints2.gridx = 0;
			marker1PatternConstraints2.gridy = 0;
			marker1PatternPanel2.setLayout(marker1PatternLayout2);

			marker1PatternPanel2.add(objectAssociatedMarker1Pattern1Button);
			objectAssociatedMarker1Pattern1Button.setSelected(false);
			marker1PatternConstraints2.gridx++;
			marker1PatternPanel2.add(objectAssociatedMarker1Pattern2Button);
			objectAssociatedMarker1Pattern2Button.setSelected(false);
			marker1PatternConstraints2.gridx++;
			marker1PatternPanel2.add(objectAssociatedMarker1Pattern3Button);
			objectAssociatedMarker1Pattern3Button.setSelected(false);
			marker1PatternConstraints2.gridx++;
			marker1PatternPanel2.add(objectAssociatedMarker1Pattern4Button);
			objectAssociatedMarker1Pattern4Button.setSelected(false);
			marker1PatternConstraints2.gridx++;

			marker1PatternPanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker1PatternLayout3 = new GridBagLayout();
			GridBagConstraints marker1PatternConstraints3 = new GridBagConstraints();
			marker1PatternConstraints3.anchor = GridBagConstraints.NORTHWEST;
			marker1PatternConstraints3.fill = GridBagConstraints.HORIZONTAL;
			marker1PatternConstraints3.gridwidth = 1;
			marker1PatternConstraints3.gridheight = 1;
			marker1PatternConstraints3.gridx = 0;
			marker1PatternConstraints3.gridy = 0;
			marker1PatternPanel3.setLayout(marker1PatternLayout3);

			marker1PatternPanel3.add(objectAssociatedMarker1PositiveLabelButton);
			objectAssociatedMarker1PositiveLabelButton.setSelected(false);
			marker1PatternConstraints3.gridx++;
			marker1PatternPanel3.add(objectAssociatedMarker1NegativeLabelButton);
			objectAssociatedMarker1NegativeLabelButton.setSelected(false);
			marker1PatternConstraints3.gridx++;
			marker1PatternPanel3.add(objectAssociatedMarker1TrainButton);
			marker1PatternConstraints3.gridx++;
			marker1PatternPanel3.add(objectAssociatedMarker1LoadButton);
			marker1PatternConstraints3.gridx++;
			marker1PatternPanel3.add(objectAssociatedMarker1SaveButton);
			marker1PatternConstraints3.gridx++;
			
			// Marker 2 pattern panel
			marker2PatternPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker2PatternLayout1 = new GridBagLayout();
			GridBagConstraints marker2PatternConstraints1 = new GridBagConstraints();
			marker2PatternConstraints1.anchor = GridBagConstraints.NORTHWEST;
			marker2PatternConstraints1.fill = GridBagConstraints.HORIZONTAL;
			marker2PatternConstraints1.gridwidth = 1;
			marker2PatternConstraints1.gridheight = 1;
			marker2PatternConstraints1.gridx = 0;
			marker2PatternConstraints1.gridy = 0;
			marker2PatternPanel1.setLayout(marker2PatternLayout1);
			marker2PatternPanel1.add(objectAssociatedMarker2Button);
			marker2PatternConstraints1.gridx++;
			marker2PatternPanel1.add(objectAssociatedMarker2ColorButton);
			marker2PatternConstraints1.gridx++;
			marker2PatternPanel1.add(objectAssociatedMarker2RemoveButton);

			marker2PatternPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker2PatternLayout2 = new GridBagLayout();
			GridBagConstraints marker2PatternConstraints2 = new GridBagConstraints();
			marker2PatternConstraints2.anchor = GridBagConstraints.NORTHWEST;
			marker2PatternConstraints2.fill = GridBagConstraints.HORIZONTAL;
			marker2PatternConstraints2.gridwidth = 1;
			marker2PatternConstraints2.gridheight = 1;
			marker2PatternConstraints2.gridx = 0;
			marker2PatternConstraints2.gridy = 0;
			marker2PatternPanel2.setLayout(marker2PatternLayout2);

			marker2PatternPanel2.add(objectAssociatedMarker2Pattern1Button);
			objectAssociatedMarker2Pattern1Button.setSelected(false);
			marker2PatternConstraints2.gridx++;
			marker2PatternPanel2.add(objectAssociatedMarker2Pattern2Button);
			objectAssociatedMarker2Pattern2Button.setSelected(false);
			marker2PatternConstraints2.gridx++;
			marker2PatternPanel2.add(objectAssociatedMarker2Pattern3Button);
			objectAssociatedMarker2Pattern3Button.setSelected(false);
			marker2PatternConstraints2.gridx++;
			marker2PatternPanel2.add(objectAssociatedMarker2Pattern4Button);
			objectAssociatedMarker2Pattern4Button.setSelected(false);
			marker2PatternConstraints2.gridx++;

			marker2PatternPanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker2PatternLayout3 = new GridBagLayout();
			GridBagConstraints marker2PatternConstraints3 = new GridBagConstraints();
			marker2PatternConstraints3.anchor = GridBagConstraints.NORTHWEST;
			marker2PatternConstraints3.fill = GridBagConstraints.HORIZONTAL;
			marker2PatternConstraints3.gridwidth = 1;
			marker2PatternConstraints3.gridheight = 1;
			marker2PatternConstraints3.gridx = 0;
			marker2PatternConstraints3.gridy = 0;
			marker2PatternPanel3.setLayout(marker2PatternLayout3);

			marker2PatternPanel3.add(objectAssociatedMarker2PositiveLabelButton);
			objectAssociatedMarker2PositiveLabelButton.setSelected(false);
			marker2PatternConstraints3.gridx++;
			marker2PatternPanel3.add(objectAssociatedMarker2NegativeLabelButton);
			objectAssociatedMarker2NegativeLabelButton.setSelected(false);
			marker2PatternConstraints3.gridx++;
			marker2PatternPanel3.add(objectAssociatedMarker2TrainButton);
			marker2PatternConstraints3.gridx++;
			marker2PatternPanel3.add(objectAssociatedMarker2LoadButton);
			marker2PatternConstraints3.gridx++;
			marker2PatternPanel3.add(objectAssociatedMarker2SaveButton);
			marker2PatternConstraints3.gridx++;

			// Marker 3 pattern panel
			marker3PatternPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker3PatternLayout1 = new GridBagLayout();
			GridBagConstraints marker3PatternConstraints1 = new GridBagConstraints();
			marker3PatternConstraints1.anchor = GridBagConstraints.NORTHWEST;
			marker3PatternConstraints1.fill = GridBagConstraints.HORIZONTAL;
			marker3PatternConstraints1.gridwidth = 1;
			marker3PatternConstraints1.gridheight = 1;
			marker3PatternConstraints1.gridx = 0;
			marker3PatternConstraints1.gridy = 0;
			marker3PatternPanel1.setLayout(marker3PatternLayout1);
			marker3PatternPanel1.add(objectAssociatedMarker3Button);
			marker3PatternConstraints1.gridx++;
			marker3PatternPanel1.add(objectAssociatedMarker3ColorButton);
			marker3PatternConstraints1.gridx++;
			marker3PatternPanel1.add(objectAssociatedMarker3RemoveButton);

			marker3PatternPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker3PatternLayout2 = new GridBagLayout();
			GridBagConstraints marker3PatternConstraints2 = new GridBagConstraints();
			marker3PatternConstraints2.anchor = GridBagConstraints.NORTHWEST;
			marker3PatternConstraints2.fill = GridBagConstraints.HORIZONTAL;
			marker3PatternConstraints2.gridwidth = 1;
			marker3PatternConstraints2.gridheight = 1;
			marker3PatternConstraints2.gridx = 0;
			marker3PatternConstraints2.gridy = 0;
			marker3PatternPanel2.setLayout(marker3PatternLayout2);

			marker3PatternPanel2.add(objectAssociatedMarker3Pattern1Button);
			objectAssociatedMarker3Pattern1Button.setSelected(false);
			marker3PatternConstraints2.gridx++;
			marker3PatternPanel2.add(objectAssociatedMarker3Pattern2Button);
			objectAssociatedMarker3Pattern2Button.setSelected(false);
			marker3PatternConstraints2.gridx++;
			marker3PatternPanel2.add(objectAssociatedMarker3Pattern3Button);
			objectAssociatedMarker3Pattern3Button.setSelected(false);
			marker3PatternConstraints2.gridx++;
			marker3PatternPanel2.add(objectAssociatedMarker3Pattern4Button);
			objectAssociatedMarker3Pattern4Button.setSelected(false);
			marker3PatternConstraints2.gridx++;

			marker3PatternPanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker3PatternLayout3 = new GridBagLayout();
			GridBagConstraints marker3PatternConstraints3 = new GridBagConstraints();
			marker3PatternConstraints3.anchor = GridBagConstraints.NORTHWEST;
			marker3PatternConstraints3.fill = GridBagConstraints.HORIZONTAL;
			marker3PatternConstraints3.gridwidth = 1;
			marker3PatternConstraints3.gridheight = 1;
			marker3PatternConstraints3.gridx = 0;
			marker3PatternConstraints3.gridy = 0;
			marker3PatternPanel3.setLayout(marker3PatternLayout3);

			marker3PatternPanel3.add(objectAssociatedMarker3PositiveLabelButton);
			objectAssociatedMarker3PositiveLabelButton.setSelected(false);
			marker3PatternConstraints3.gridx++;
			marker3PatternPanel3.add(objectAssociatedMarker3NegativeLabelButton);
			objectAssociatedMarker3NegativeLabelButton.setSelected(false);
			marker3PatternConstraints3.gridx++;
			marker3PatternPanel3.add(objectAssociatedMarker3TrainButton);
			marker3PatternConstraints3.gridx++;
			marker3PatternPanel3.add(objectAssociatedMarker3LoadButton);
			marker3PatternConstraints3.gridx++;
			marker3PatternPanel3.add(objectAssociatedMarker3SaveButton);
			marker3PatternConstraints3.gridx++;

			// Marker 4 pattern panel
			marker4PatternPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker4PatternLayout1 = new GridBagLayout();
			GridBagConstraints marker4PatternConstraints1 = new GridBagConstraints();
			marker4PatternConstraints1.anchor = GridBagConstraints.NORTHWEST;
			marker4PatternConstraints1.fill = GridBagConstraints.HORIZONTAL;
			marker4PatternConstraints1.gridwidth = 1;
			marker4PatternConstraints1.gridheight = 1;
			marker4PatternConstraints1.gridx = 0;
			marker4PatternConstraints1.gridy = 0;
			marker4PatternPanel1.setLayout(marker4PatternLayout1);
			marker4PatternPanel1.add(objectAssociatedMarker4Button);
			marker4PatternConstraints1.gridx++;
			marker4PatternPanel1.add(objectAssociatedMarker4ColorButton);
			marker4PatternConstraints1.gridx++;
			marker4PatternPanel1.add(objectAssociatedMarker4RemoveButton);

			marker4PatternPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker4PatternLayout2 = new GridBagLayout();
			GridBagConstraints marker4PatternConstraints2 = new GridBagConstraints();
			marker4PatternConstraints2.anchor = GridBagConstraints.NORTHWEST;
			marker4PatternConstraints2.fill = GridBagConstraints.HORIZONTAL;
			marker4PatternConstraints2.gridwidth = 1;
			marker4PatternConstraints2.gridheight = 1;
			marker4PatternConstraints2.gridx = 0;
			marker4PatternConstraints2.gridy = 0;
			marker4PatternPanel2.setLayout(marker4PatternLayout2);

			marker4PatternPanel2.add(objectAssociatedMarker4Pattern1Button);
			objectAssociatedMarker4Pattern1Button.setSelected(false);
			marker4PatternConstraints2.gridx++;
			marker4PatternPanel2.add(objectAssociatedMarker4Pattern2Button);
			objectAssociatedMarker4Pattern2Button.setSelected(false);
			marker4PatternConstraints2.gridx++;
			marker4PatternPanel2.add(objectAssociatedMarker4Pattern3Button);
			objectAssociatedMarker4Pattern3Button.setSelected(false);
			marker4PatternConstraints2.gridx++;
			marker4PatternPanel2.add(objectAssociatedMarker4Pattern4Button);
			objectAssociatedMarker4Pattern4Button.setSelected(false);
			marker4PatternConstraints2.gridx++;

			marker4PatternPanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker4PatternLayout3 = new GridBagLayout();
			GridBagConstraints marker4PatternConstraints3 = new GridBagConstraints();
			marker4PatternConstraints3.anchor = GridBagConstraints.NORTHWEST;
			marker4PatternConstraints3.fill = GridBagConstraints.HORIZONTAL;
			marker4PatternConstraints3.gridwidth = 1;
			marker4PatternConstraints3.gridheight = 1;
			marker4PatternConstraints3.gridx = 0;
			marker4PatternConstraints3.gridy = 0;
			marker4PatternPanel3.setLayout(marker4PatternLayout3);

			marker4PatternPanel3.add(objectAssociatedMarker4PositiveLabelButton);
			objectAssociatedMarker4PositiveLabelButton.setSelected(false);
			marker4PatternConstraints3.gridx++;
			marker4PatternPanel3.add(objectAssociatedMarker4NegativeLabelButton);
			objectAssociatedMarker4NegativeLabelButton.setSelected(false);
			marker4PatternConstraints3.gridx++;
			marker4PatternPanel3.add(objectAssociatedMarker4TrainButton);
			marker4PatternConstraints3.gridx++;
			marker4PatternPanel3.add(objectAssociatedMarker4LoadButton);
			marker4PatternConstraints3.gridx++;
			marker4PatternPanel3.add(objectAssociatedMarker4SaveButton);
			marker4PatternConstraints3.gridx++;

			// Marker 5 pattern panel
			marker5PatternPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker5PatternLayout1 = new GridBagLayout();
			GridBagConstraints marker5PatternConstraints1 = new GridBagConstraints();
			marker5PatternConstraints1.anchor = GridBagConstraints.NORTHWEST;
			marker5PatternConstraints1.fill = GridBagConstraints.HORIZONTAL;
			marker5PatternConstraints1.gridwidth = 1;
			marker5PatternConstraints1.gridheight = 1;
			marker5PatternConstraints1.gridx = 0;
			marker5PatternConstraints1.gridy = 0;
			marker5PatternPanel1.setLayout(marker5PatternLayout1);
			marker5PatternPanel1.add(objectAssociatedMarker5Button);
			marker5PatternConstraints1.gridx++;
			marker5PatternPanel1.add(objectAssociatedMarker5ColorButton);
			marker5PatternConstraints1.gridx++;
			marker5PatternPanel1.add(objectAssociatedMarker5RemoveButton);

			marker5PatternPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker5PatternLayout2 = new GridBagLayout();
			GridBagConstraints marker5PatternConstraints2 = new GridBagConstraints();
			marker5PatternConstraints2.anchor = GridBagConstraints.NORTHWEST;
			marker5PatternConstraints2.fill = GridBagConstraints.HORIZONTAL;
			marker5PatternConstraints2.gridwidth = 1;
			marker5PatternConstraints2.gridheight = 1;
			marker5PatternConstraints2.gridx = 0;
			marker5PatternConstraints2.gridy = 0;
			marker5PatternPanel2.setLayout(marker5PatternLayout2);

			marker5PatternPanel2.add(objectAssociatedMarker5Pattern1Button);
			objectAssociatedMarker5Pattern1Button.setSelected(false);
			marker5PatternConstraints2.gridx++;
			marker5PatternPanel2.add(objectAssociatedMarker5Pattern2Button);
			objectAssociatedMarker5Pattern2Button.setSelected(false);
			marker5PatternConstraints2.gridx++;
			marker5PatternPanel2.add(objectAssociatedMarker5Pattern3Button);
			objectAssociatedMarker5Pattern3Button.setSelected(false);
			marker5PatternConstraints2.gridx++;
			marker5PatternPanel2.add(objectAssociatedMarker5Pattern4Button);
			objectAssociatedMarker5Pattern4Button.setSelected(false);
			marker5PatternConstraints2.gridx++;

			marker5PatternPanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker5PatternLayout3 = new GridBagLayout();
			GridBagConstraints marker5PatternConstraints3 = new GridBagConstraints();
			marker5PatternConstraints3.anchor = GridBagConstraints.NORTHWEST;
			marker5PatternConstraints3.fill = GridBagConstraints.HORIZONTAL;
			marker5PatternConstraints3.gridwidth = 1;
			marker5PatternConstraints3.gridheight = 1;
			marker5PatternConstraints3.gridx = 0;
			marker5PatternConstraints3.gridy = 0;
			marker5PatternPanel3.setLayout(marker5PatternLayout3);

			marker5PatternPanel3.add(objectAssociatedMarker5PositiveLabelButton);
			objectAssociatedMarker5PositiveLabelButton.setSelected(false);
			marker5PatternConstraints3.gridx++;
			marker5PatternPanel3.add(objectAssociatedMarker5NegativeLabelButton);
			objectAssociatedMarker5NegativeLabelButton.setSelected(false);
			marker5PatternConstraints3.gridx++;
			marker5PatternPanel3.add(objectAssociatedMarker5TrainButton);
			marker5PatternConstraints3.gridx++;
			marker5PatternPanel3.add(objectAssociatedMarker5LoadButton);
			marker5PatternConstraints3.gridx++;
			marker5PatternPanel3.add(objectAssociatedMarker5SaveButton);
			marker5PatternConstraints3.gridx++;

			// Marker 6 pattern panel
			marker6PatternPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker6PatternLayout1 = new GridBagLayout();
			GridBagConstraints marker6PatternConstraints1 = new GridBagConstraints();
			marker6PatternConstraints1.anchor = GridBagConstraints.NORTHWEST;
			marker6PatternConstraints1.fill = GridBagConstraints.HORIZONTAL;
			marker6PatternConstraints1.gridwidth = 1;
			marker6PatternConstraints1.gridheight = 1;
			marker6PatternConstraints1.gridx = 0;
			marker6PatternConstraints1.gridy = 0;
			marker6PatternPanel1.setLayout(marker6PatternLayout1);
			marker6PatternPanel1.add(objectAssociatedMarker6Button);
			marker6PatternConstraints1.gridx++;
			marker6PatternPanel1.add(objectAssociatedMarker6ColorButton);
			marker6PatternConstraints1.gridx++;
			marker6PatternPanel1.add(objectAssociatedMarker6RemoveButton);

			marker6PatternPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker6PatternLayout2 = new GridBagLayout();
			GridBagConstraints marker6PatternConstraints2 = new GridBagConstraints();
			marker6PatternConstraints2.anchor = GridBagConstraints.NORTHWEST;
			marker6PatternConstraints2.fill = GridBagConstraints.HORIZONTAL;
			marker6PatternConstraints2.gridwidth = 1;
			marker6PatternConstraints2.gridheight = 1;
			marker6PatternConstraints2.gridx = 0;
			marker6PatternConstraints2.gridy = 0;
			marker6PatternPanel2.setLayout(marker6PatternLayout2);

			marker6PatternPanel2.add(objectAssociatedMarker6Pattern1Button);
			objectAssociatedMarker6Pattern1Button.setSelected(false);
			marker6PatternConstraints2.gridx++;
			marker6PatternPanel2.add(objectAssociatedMarker6Pattern2Button);
			objectAssociatedMarker6Pattern2Button.setSelected(false);
			marker6PatternConstraints2.gridx++;
			marker6PatternPanel2.add(objectAssociatedMarker6Pattern3Button);
			objectAssociatedMarker6Pattern3Button.setSelected(false);
			marker6PatternConstraints2.gridx++;
			marker6PatternPanel2.add(objectAssociatedMarker6Pattern4Button);
			objectAssociatedMarker6Pattern4Button.setSelected(false);
			marker6PatternConstraints2.gridx++;

			marker6PatternPanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker6PatternLayout3 = new GridBagLayout();
			GridBagConstraints marker6PatternConstraints3 = new GridBagConstraints();
			marker6PatternConstraints3.anchor = GridBagConstraints.NORTHWEST;
			marker6PatternConstraints3.fill = GridBagConstraints.HORIZONTAL;
			marker6PatternConstraints3.gridwidth = 1;
			marker6PatternConstraints3.gridheight = 1;
			marker6PatternConstraints3.gridx = 0;
			marker6PatternConstraints3.gridy = 0;
			marker6PatternPanel3.setLayout(marker6PatternLayout3);

			marker6PatternPanel3.add(objectAssociatedMarker6PositiveLabelButton);
			objectAssociatedMarker6PositiveLabelButton.setSelected(false);
			marker6PatternConstraints3.gridx++;
			marker6PatternPanel3.add(objectAssociatedMarker6NegativeLabelButton);
			objectAssociatedMarker6NegativeLabelButton.setSelected(false);
			marker6PatternConstraints3.gridx++;
			marker6PatternPanel3.add(objectAssociatedMarker6TrainButton);
			marker6PatternConstraints3.gridx++;
			marker6PatternPanel3.add(objectAssociatedMarker6LoadButton);
			marker6PatternConstraints3.gridx++;
			marker6PatternPanel3.add(objectAssociatedMarker6SaveButton);
			marker6PatternConstraints3.gridx++;

			// Marker 7 pattern panel
			marker7PatternPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker7PatternLayout1 = new GridBagLayout();
			GridBagConstraints marker7PatternConstraints1 = new GridBagConstraints();
			marker7PatternConstraints1.anchor = GridBagConstraints.NORTHWEST;
			marker7PatternConstraints1.fill = GridBagConstraints.HORIZONTAL;
			marker7PatternConstraints1.gridwidth = 1;
			marker7PatternConstraints1.gridheight = 1;
			marker7PatternConstraints1.gridx = 0;
			marker7PatternConstraints1.gridy = 0;
			marker7PatternPanel1.setLayout(marker7PatternLayout1);
			marker7PatternPanel1.add(objectAssociatedMarker7Button);
			marker7PatternConstraints1.gridx++;
			marker7PatternPanel1.add(objectAssociatedMarker7ColorButton);
			marker7PatternConstraints1.gridx++;
			marker7PatternPanel1.add(objectAssociatedMarker7RemoveButton);

			marker7PatternPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker7PatternLayout2 = new GridBagLayout();
			GridBagConstraints marker7PatternConstraints2 = new GridBagConstraints();
			marker7PatternConstraints2.anchor = GridBagConstraints.NORTHWEST;
			marker7PatternConstraints2.fill = GridBagConstraints.HORIZONTAL;
			marker7PatternConstraints2.gridwidth = 1;
			marker7PatternConstraints2.gridheight = 1;
			marker7PatternConstraints2.gridx = 0;
			marker7PatternConstraints2.gridy = 0;
			marker7PatternPanel2.setLayout(marker7PatternLayout2);

			marker7PatternPanel2.add(objectAssociatedMarker7Pattern1Button);
			objectAssociatedMarker7Pattern1Button.setSelected(false);
			marker7PatternConstraints2.gridx++;
			marker7PatternPanel2.add(objectAssociatedMarker7Pattern2Button);
			objectAssociatedMarker7Pattern2Button.setSelected(false);
			marker7PatternConstraints2.gridx++;
			marker7PatternPanel2.add(objectAssociatedMarker7Pattern3Button);
			objectAssociatedMarker7Pattern3Button.setSelected(false);
			marker7PatternConstraints2.gridx++;
			marker7PatternPanel2.add(objectAssociatedMarker7Pattern4Button);
			objectAssociatedMarker7Pattern4Button.setSelected(false);
			marker7PatternConstraints2.gridx++;

			marker7PatternPanel3.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout marker7PatternLayout3 = new GridBagLayout();
			GridBagConstraints marker7PatternConstraints3 = new GridBagConstraints();
			marker7PatternConstraints3.anchor = GridBagConstraints.NORTHWEST;
			marker7PatternConstraints3.fill = GridBagConstraints.HORIZONTAL;
			marker7PatternConstraints3.gridwidth = 1;
			marker7PatternConstraints3.gridheight = 1;
			marker7PatternConstraints3.gridx = 0;
			marker7PatternConstraints3.gridy = 0;
			marker7PatternPanel3.setLayout(marker7PatternLayout3);

			marker7PatternPanel3.add(objectAssociatedMarker7PositiveLabelButton);
			objectAssociatedMarker7PositiveLabelButton.setSelected(false);
			marker7PatternConstraints3.gridx++;
			marker7PatternPanel3.add(objectAssociatedMarker7NegativeLabelButton);
			objectAssociatedMarker7NegativeLabelButton.setSelected(false);
			marker7PatternConstraints3.gridx++;
			marker7PatternPanel3.add(objectAssociatedMarker7TrainButton);
			marker7PatternConstraints3.gridx++;
			marker7PatternPanel3.add(objectAssociatedMarker7LoadButton);
			marker7PatternConstraints3.gridx++;
			marker7PatternPanel3.add(objectAssociatedMarker7SaveButton);
			marker7PatternConstraints3.gridx++;

			// load Image And Segmentation Panel to annotate other + and - cells
			loadImageAndSegmentationConstraints.anchor = GridBagConstraints.NORTHWEST;
			loadImageAndSegmentationConstraints.fill = GridBagConstraints.HORIZONTAL;
			loadImageAndSegmentationConstraints.gridwidth = 1;
			loadImageAndSegmentationConstraints.gridheight = 1;
			loadImageAndSegmentationConstraints.gridx = 0;
			loadImageAndSegmentationConstraints.gridy = 0;
			loadImageAndSegmentationPanel.setLayout(loadImageAndSegmentationLayout);
			if(Prefs.getGuiScale()==1.0){
				loadImageAndSegmentationPanel.setBorder(BorderFactory.createTitledBorder("Load image & segmentation"));
			}
			else{
				JTextArea loadImageAndSegmentationTitle = new JTextArea("Load image & segmentation");
				scale(loadImageAndSegmentationTitle);
				loadImageAndSegmentationPanel.add(loadImageAndSegmentationTitle, loadImageAndSegmentationConstraints);
				loadImageAndSegmentationConstraints.gridy++;
			}
			loadImageAndSegmentationPanel.add(loadImageAndSegmentationButton,loadImageAndSegmentationConstraints);
			
			// Object associated markers panel
			objectAssociatedMarkersConstraints.anchor = GridBagConstraints.NORTHWEST;
			objectAssociatedMarkersConstraints.fill = GridBagConstraints.HORIZONTAL;
			objectAssociatedMarkersConstraints.gridwidth = 1;
			objectAssociatedMarkersConstraints.gridheight = 1;
			objectAssociatedMarkersConstraints.gridx = 0;
			objectAssociatedMarkersConstraints.gridy = 0;
			objectAssociatedMarkersPanel.setLayout(objectAssociatedMarkersLayout);

			if(Prefs.getGuiScale()==1.0){
				objectAssociatedMarkersPanel.setBorder(BorderFactory.createTitledBorder("Objects"));
			}
			else{
				JTextArea objectAssociatedMarkersTitle = new JTextArea("Objects");
				scale(objectAssociatedMarkersTitle);
				objectAssociatedMarkersPanel.add(objectAssociatedMarkersTitle, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
			}
			objectAssociatedMarkersPanel.add(filePanel2,objectAssociatedMarkersConstraints);
			objectAssociatedMarkersConstraints.gridy++;
			objectAssociatedMarkersPanel.add(addObjectAssociatedMarkerButton,objectAssociatedMarkersConstraints);
			objectAssociatedMarkersConstraints.gridy++;

			if(numOfObjectAssociatedMarkers>0) {
				objectAssociatedMarker1Button.setSelected(false);
				objectAssociatedMarkersPanel.add(marker1PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				if(methodToIdentifyObjectAssociatedMarkers[0]==2){
					objectAssociatedMarkersPanel.add(marker1PatternPanel3, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
				else{
					objectAssociatedMarkersPanel.add(marker1PatternPanel2, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
			}
			if(numOfObjectAssociatedMarkers>1) {
				objectAssociatedMarker2Button.setSelected(false);
				objectAssociatedMarkersPanel.add(marker2PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				if(methodToIdentifyObjectAssociatedMarkers[1]==2){
					objectAssociatedMarkersPanel.add(marker2PatternPanel3, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
				else{
					objectAssociatedMarkersPanel.add(marker2PatternPanel2, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
			}
			if(numOfObjectAssociatedMarkers>2) {
				objectAssociatedMarker3Button.setSelected(false);
				objectAssociatedMarkersPanel.add(marker3PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				if(methodToIdentifyObjectAssociatedMarkers[2]==2){
					objectAssociatedMarkersPanel.add(marker3PatternPanel3, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
				else{
					objectAssociatedMarkersPanel.add(marker3PatternPanel2, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
			}
			if(numOfObjectAssociatedMarkers>3) {
				objectAssociatedMarker4Button.setSelected(false);
				objectAssociatedMarkersPanel.add(marker4PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				if(methodToIdentifyObjectAssociatedMarkers[3]==2){
					objectAssociatedMarkersPanel.add(marker4PatternPanel3, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
				else{
					objectAssociatedMarkersPanel.add(marker4PatternPanel2, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
			}
			if(numOfObjectAssociatedMarkers>4) {
				objectAssociatedMarker5Button.setSelected(false);
				objectAssociatedMarkersPanel.add(marker5PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				if(methodToIdentifyObjectAssociatedMarkers[4]==2){
					objectAssociatedMarkersPanel.add(marker5PatternPanel3, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
				else{
					objectAssociatedMarkersPanel.add(marker5PatternPanel2, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
			}
			if(numOfObjectAssociatedMarkers>5) {
				objectAssociatedMarker6Button.setSelected(false);
				objectAssociatedMarkersPanel.add(marker6PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				if(methodToIdentifyObjectAssociatedMarkers[5]==2){
					objectAssociatedMarkersPanel.add(marker6PatternPanel3, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
				else{
					objectAssociatedMarkersPanel.add(marker6PatternPanel2, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
			}
			if(numOfObjectAssociatedMarkers>6) {
				objectAssociatedMarker7Button.setSelected(false);
				objectAssociatedMarkersPanel.add(marker7PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				if(methodToIdentifyObjectAssociatedMarkers[6]==2){
					objectAssociatedMarkersPanel.add(marker7PatternPanel3, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
				else{
					objectAssociatedMarkersPanel.add(marker7PatternPanel2, objectAssociatedMarkersConstraints);
					objectAssociatedMarkersConstraints.gridy++;
				}
			}

			if(currentMode==1) {Toolbar.getInstance().setTool(Toolbar.POINT);}

			// Visualization panel 1
			GridBagLayout visualizationLayout1 = new GridBagLayout();
			GridBagConstraints visualizationConstraints1 = new GridBagConstraints();
			visualizationConstraints1.anchor = GridBagConstraints.NORTHWEST;
			visualizationConstraints1.fill = GridBagConstraints.HORIZONTAL;
			visualizationConstraints1.gridwidth = 1;
			visualizationConstraints1.gridheight = 1;
			visualizationConstraints1.gridx = 0;
			visualizationConstraints1.gridy = 0;

			visualizationPanel1.setLayout(visualizationLayout1);
			if(Prefs.getGuiScale()==1.0){
				visualizationPanel1.setBorder(BorderFactory.createTitledBorder("Channel selection"));
			}
			else{
				JTextArea visualizationTitle = new JTextArea("Channel selection");
				scale(visualizationTitle);
				visualizationPanel1.add(visualizationTitle, visualizationConstraints1);
				visualizationConstraints1.gridx++;
				JTextArea blankTitle = new JTextArea("");
				scale(blankTitle);
				visualizationPanel1.add(blankTitle, visualizationConstraints1);
				visualizationConstraints1.gridy++;
				visualizationConstraints1.gridx=0;
			}
			visualizationPanel1.add(visualizeChannel1Button1, visualizationConstraints1);
			visualizationConstraints1.gridx++;
			visualizationPanel1.add(visualizeChannel1onlyButton1, visualizationConstraints1);
			visualizationConstraints1.gridx = 0;			
			visualizationConstraints1.gridy++;
			initializeVisualizeChannelButtons1();

			if(numOfChannels>1) {
				visualizationPanel1.add(visualizeChannel2Button1, visualizationConstraints1);
				visualizationConstraints1.gridx++;
				visualizationPanel1.add(visualizeChannel2onlyButton1, visualizationConstraints1);
				visualizationConstraints1.gridx = 0;			
				visualizationConstraints1.gridy++;
			}
			if(numOfChannels>2) {
				visualizationPanel1.add(visualizeChannel3Button1, visualizationConstraints1);
				visualizationConstraints1.gridx++;
				visualizationPanel1.add(visualizeChannel3onlyButton1, visualizationConstraints1);
				visualizationConstraints1.gridx = 0;			
				visualizationConstraints1.gridy++;
			}
			if(numOfChannels>3) {
				visualizationPanel1.add(visualizeChannel4Button1, visualizationConstraints1);
				visualizationConstraints1.gridx++;
				visualizationPanel1.add(visualizeChannel4onlyButton1, visualizationConstraints1);
				visualizationConstraints1.gridx = 0;			
				visualizationConstraints1.gridy++;
			}
			if(numOfChannels>4) {
				visualizationPanel1.add(visualizeChannel5Button1, visualizationConstraints1);
				visualizationConstraints1.gridx++;
				visualizationPanel1.add(visualizeChannel5onlyButton1, visualizationConstraints1);
				visualizationConstraints1.gridx = 0;			
				visualizationConstraints1.gridy++;
			}
			if(numOfChannels>5) {
				visualizationPanel1.add(visualizeChannel6Button1, visualizationConstraints1);
				visualizationConstraints1.gridx++;
				visualizationPanel1.add(visualizeChannel6onlyButton1, visualizationConstraints1);
				visualizationConstraints1.gridx = 0;			
				visualizationConstraints1.gridy++;
			}
			if(numOfChannels>6) {
				visualizationPanel1.add(visualizeChannel7Button1, visualizationConstraints1);
				visualizationConstraints1.gridx++;
				visualizationPanel1.add(visualizeChannel7onlyButton1, visualizationConstraints1);
				visualizationConstraints1.gridx = 0;			
				visualizationConstraints1.gridy++;
			}
			visualizationPanel1.add(visualizeAllChannelsButton1, visualizationConstraints1);
			updateVisualizeChannelButtons1((byte)20);
			visualizationConstraints1.gridy++;
			visualizeAllChannelsButton1.setSelected(true);
			
			
			// Visualization panel 2
			GridBagLayout visualizationLayout2 = new GridBagLayout();
			GridBagConstraints visualizationConstraints2 = new GridBagConstraints();
			visualizationConstraints2.anchor = GridBagConstraints.NORTHWEST;
			visualizationConstraints2.fill = GridBagConstraints.HORIZONTAL;
			visualizationConstraints2.gridwidth = 1;
			visualizationConstraints2.gridheight = 1;
			visualizationConstraints2.gridx = 0;
			visualizationConstraints2.gridy = 0;
			visualizationPanel2.setLayout(visualizationLayout2);

			if(Prefs.getGuiScale()==1.0){
				visualizationPanel2.setBorder(BorderFactory.createTitledBorder("Channel selection"));
			}
			else{
				JTextArea visualizationTitle = new JTextArea("Channel selection");
				scale(visualizationTitle);
				visualizationPanel2.add(visualizationTitle, visualizationConstraints2);
				visualizationConstraints2.gridx++;
				JTextArea blankTitle = new JTextArea("");
				scale(blankTitle);
				visualizationPanel2.add(blankTitle, visualizationConstraints2);
				visualizationConstraints2.gridy++;
				visualizationConstraints2.gridx=0;
			}
			visualizationPanel2.add(visualizeChannel1Button2, visualizationConstraints2);
			visualizationConstraints2.gridx++;
			visualizationPanel2.add(visualizeChannel1onlyButton2, visualizationConstraints2);
			visualizationConstraints2.gridx = 0;
			visualizationConstraints2.gridy++;
			initializeVisualizeChannelButtons2();
			if(numOfChannels>1) {
				visualizationPanel2.add(visualizeChannel2Button2, visualizationConstraints2);
				visualizationConstraints2.gridx++;
				visualizationPanel2.add(visualizeChannel2onlyButton2, visualizationConstraints2);
				visualizationConstraints2.gridx = 0;
				visualizationConstraints2.gridy++;
			}
			if(numOfChannels>2) {
				visualizationPanel2.add(visualizeChannel3Button2, visualizationConstraints2);
				visualizationConstraints2.gridx++;
				visualizationPanel2.add(visualizeChannel3onlyButton2, visualizationConstraints2);
				visualizationConstraints2.gridx = 0;
				visualizationConstraints2.gridy++;
			}
			if(numOfChannels>3) {
				visualizationPanel2.add(visualizeChannel4Button2, visualizationConstraints2);
				visualizationConstraints2.gridx++;
				visualizationPanel2.add(visualizeChannel4onlyButton2, visualizationConstraints2);
				visualizationConstraints2.gridx = 0;
				visualizationConstraints2.gridy++;
			}
			if(numOfChannels>4) {
				visualizationPanel2.add(visualizeChannel5Button2, visualizationConstraints2);
				visualizationConstraints2.gridx++;
				visualizationPanel2.add(visualizeChannel5onlyButton2, visualizationConstraints2);
				visualizationConstraints2.gridx = 0;
				visualizationConstraints2.gridy++;
			}
			if(numOfChannels>5) {
				visualizationPanel2.add(visualizeChannel6Button2, visualizationConstraints2);
				visualizationConstraints2.gridx++;
				visualizationPanel2.add(visualizeChannel6onlyButton2, visualizationConstraints2);
				visualizationConstraints2.gridx = 0;
				visualizationConstraints2.gridy++;
			}
			if(numOfChannels>6) {
				visualizationPanel2.add(visualizeChannel7Button2, visualizationConstraints2);
				visualizationConstraints2.gridx++;
				visualizationPanel2.add(visualizeChannel7onlyButton2, visualizationConstraints2);
				visualizationConstraints2.gridx = 0;
				visualizationConstraints2.gridy++;
			}
			visualizationPanel2.add(visualizeAllChannelsButton2, visualizationConstraints2);
			visualizationConstraints2.gridy++;
			if(currentDisplayedChannel > (-1)){
				displayImage.setDisplayMode(IJ.COMPOSITE);
				displayImage.setPosition(currentDisplayedChannel+1, displayImage.getSlice(), displayImage.getFrame());
				//displayImage.setDisplayRange(originalLUT[currentDisplayedChannel].min, originalLUT[currentDisplayedChannel].max);
				displayImage.updateAndDraw();
				currentDisplayedChannel = -1;
			}
			visualizeAllChannelsButton2.setSelected(true);

			// Visualization panel 3
			GridBagLayout visualizationLayout3 = new GridBagLayout();
			GridBagConstraints visualizationConstraints3 = new GridBagConstraints();
			visualizationConstraints3.anchor = GridBagConstraints.NORTHWEST;
			visualizationConstraints3.fill = GridBagConstraints.HORIZONTAL;
			visualizationConstraints3.gridwidth = 1;
			visualizationConstraints3.gridheight = 1;
			visualizationConstraints3.gridx = 0;
			visualizationConstraints3.gridy = 0;

			visualizationPanel3.setLayout(visualizationLayout1);
			if(Prefs.getGuiScale()==1.0){
				visualizationPanel3.setBorder(BorderFactory.createTitledBorder("Object and area visualization"));
			}
			else{
				JTextArea visualizationTitle = new JTextArea("Object and area visualization");
				scale(visualizationTitle);
				visualizationPanel3.add(visualizationTitle, visualizationConstraints3);
				visualizationConstraints3.gridx++;
				JTextArea blankTitle = new JTextArea("");
				scale(blankTitle);
				visualizationPanel3.add(blankTitle, visualizationConstraints3);
				visualizationConstraints3.gridy++;
				visualizationConstraints3.gridx=0;
			}
			visualizationPanel3.add(visualizeObjectsButton1, visualizationConstraints3);
			visualizationConstraints3.gridx++;
			visualizationPanel3.add(visualizeAreasButton1, visualizationConstraints3);

			// Visualization panel 4
			GridBagLayout visualizationLayout4 = new GridBagLayout();
			GridBagConstraints visualizationConstraints4 = new GridBagConstraints();
			visualizationConstraints4.anchor = GridBagConstraints.NORTHWEST;
			visualizationConstraints4.fill = GridBagConstraints.HORIZONTAL;
			visualizationConstraints4.gridwidth = 1;
			visualizationConstraints4.gridheight = 1;
			visualizationConstraints4.gridx = 0;
			visualizationConstraints4.gridy = 0;

			visualizationPanel4.setLayout(visualizationLayout1);
			if(Prefs.getGuiScale()==1.0){
				visualizationPanel4.setBorder(BorderFactory.createTitledBorder("Object and area visualization"));
			}
			else{
				JTextArea visualizationTitle = new JTextArea("Object and area visualization");
				scale(visualizationTitle);
				visualizationPanel4.add(visualizationTitle, visualizationConstraints4);
				visualizationConstraints4.gridx++;
				JTextArea blankTitle = new JTextArea("");
				scale(blankTitle);
				visualizationPanel4.add(blankTitle, visualizationConstraints4);
				visualizationConstraints4.gridy++;
				visualizationConstraints4.gridx=0;
			}
			visualizationPanel4.add(visualizeObjectsButton2, visualizationConstraints4);
			visualizationConstraints4.gridx++;
			visualizationPanel4.add(visualizeAreasButton2, visualizationConstraints4);

			// Annotation panel 1
			GridBagLayout annotationLayout = new GridBagLayout();
			GridBagConstraints annotationConstraints = new GridBagConstraints();
			annotationConstraints.anchor = GridBagConstraints.NORTHWEST;
			annotationConstraints.fill = GridBagConstraints.HORIZONTAL;
			annotationConstraints.gridwidth = 1;
			annotationConstraints.gridheight = 1;
			annotationConstraints.gridx = 0;
			annotationConstraints.gridy = 0;
			//annotationConstraints.insets = new Insets(5, 5, 6, 6);
			annotationPanel1.setLayout(annotationLayout);

			if(Prefs.getGuiScale()==1.0){
				annotationPanel1.setBorder(BorderFactory.createTitledBorder("Object annotation"));
			}
			else{
				JTextArea annotationPanel1Title = new JTextArea("Object annotation");
				scale(annotationPanel1Title);
				annotationPanel1.add(annotationPanel1Title, annotationConstraints);
				annotationConstraints.gridx++;
				JTextArea blankTitle = new JTextArea("");
				scale(blankTitle);
				annotationPanel1.add(blankTitle, annotationConstraints);
				annotationConstraints.gridy++;
				annotationConstraints.gridx=0;
			}
			annotationPanel1.add(newObjectButton, annotationConstraints);
			annotationConstraints.gridx++;
			newObjectButton.setSelected(true);
			if(currentMode==0) {Toolbar.getInstance().setTool(Toolbar.FREEROI);}

			annotationPanel1.add(removeObjectButton, annotationConstraints);
			annotationConstraints.gridy++;
			annotationConstraints.gridx=0;
			removeObjectButton.setSelected(false);
			annotationPanel1.add(mergeObjectsButton, annotationConstraints);
			annotationConstraints.gridx++;
			mergeObjectsButton.setSelected(false);
			annotationPanel1.add(splitObjectsButton, annotationConstraints);
			annotationConstraints.gridy++;
			annotationConstraints.gridx=0;
			splitObjectsButton.setSelected(false);
			annotationPanel1.add(swapObjectClassButton, annotationConstraints);
			annotationConstraints.gridy++;
			swapObjectClassButton.setSelected(false);

			// Classes panel
			classesConstraints.anchor = GridBagConstraints.NORTHWEST;
			classesConstraints.fill = GridBagConstraints.HORIZONTAL;
			classesConstraints.gridwidth = 1;
			classesConstraints.gridheight = 1;
			classesConstraints.gridx = 0;
			classesConstraints.gridy = 0;
			//classesConstraints.insets = new Insets(5, 5, 6, 6);
			classesPanel.setLayout(classesLayout);

			if(Prefs.getGuiScale()==1.0){
				classesPanel.setBorder(BorderFactory.createTitledBorder("Object classes"));
			}
			else{
				JTextArea classesPanelTitle = new JTextArea("Object classes");
				scale(classesPanelTitle);
				classesPanel.add(classesPanelTitle, classesConstraints);
				classesConstraints.gridy++;
			}
			classesPanel.add(filePanel1,classesConstraints);
			classesConstraints.gridy++;
			classesPanel.add(addClassButton,classesConstraints);
			classesConstraints.gridy++;


			class1Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout class1Layout = new GridBagLayout();
			GridBagConstraints class1Constraints = new GridBagConstraints();
			class1Constraints.anchor = GridBagConstraints.NORTHWEST;
			class1Constraints.fill = GridBagConstraints.HORIZONTAL;
			class1Constraints.gridwidth = 1;
			class1Constraints.gridheight = 1;
			class1Constraints.gridx = 0;
			class1Constraints.gridy = 0;
			class1Panel.setLayout(class1Layout);
			class1Panel.add(class1Button);
			class1Constraints.gridx++;
			class1Panel.add(class1ColorButton);
			class1Constraints.gridx++;
			class1Panel.add(class1RemoveButton);

			class2Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout class2Layout = new GridBagLayout();
			GridBagConstraints class2Constraints = new GridBagConstraints();
			class2Constraints.anchor = GridBagConstraints.NORTHWEST;
			class2Constraints.fill = GridBagConstraints.HORIZONTAL;
			class2Constraints.gridwidth = 1;
			class2Constraints.gridheight = 1;
			class2Constraints.gridx = 0;
			class2Constraints.gridy = 0;
			class2Panel.setLayout(class2Layout);
			class2Panel.add(class2Button);
			class2Constraints.gridx++;
			class2Panel.add(class2ColorButton);
			class2Constraints.gridx++;
			class2Panel.add(class2RemoveButton);

			class3Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout class3Layout = new GridBagLayout();
			GridBagConstraints class3Constraints = new GridBagConstraints();
			class3Constraints.anchor = GridBagConstraints.NORTHWEST;
			class3Constraints.fill = GridBagConstraints.HORIZONTAL;
			class3Constraints.gridwidth = 1;
			class3Constraints.gridheight = 1;
			class3Constraints.gridx = 0;
			class3Constraints.gridy = 0;
			class3Panel.setLayout(class3Layout);
			class3Panel.add(class3Button);
			class3Constraints.gridx++;
			class3Panel.add(class3ColorButton);
			class3Constraints.gridx++;
			class3Panel.add(class3RemoveButton);

			class4Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout class4Layout = new GridBagLayout();
			GridBagConstraints class4Constraints = new GridBagConstraints();
			class4Constraints.anchor = GridBagConstraints.NORTHWEST;
			class4Constraints.fill = GridBagConstraints.HORIZONTAL;
			class4Constraints.gridwidth = 1;
			class4Constraints.gridheight = 1;
			class4Constraints.gridx = 0;
			class4Constraints.gridy = 0;
			class4Panel.setLayout(class4Layout);
			class4Panel.add(class4Button);
			class4Constraints.gridx++;
			class4Panel.add(class4ColorButton);
			class4Constraints.gridx++;
			class4Panel.add(class4RemoveButton);

			class5Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout class5Layout = new GridBagLayout();
			GridBagConstraints class5Constraints = new GridBagConstraints();
			class5Constraints.anchor = GridBagConstraints.NORTHWEST;
			class5Constraints.fill = GridBagConstraints.HORIZONTAL;
			class5Constraints.gridwidth = 1;
			class5Constraints.gridheight = 1;
			class5Constraints.gridx = 0;
			class5Constraints.gridy = 0;
			class5Panel.setLayout(class5Layout);
			class5Panel.add(class5Button);
			class5Constraints.gridx++;
			class5Panel.add(class5ColorButton);
			class5Constraints.gridx++;
			class5Panel.add(class5RemoveButton);

			classesPanel.add(class1Panel,classesConstraints);
			classesConstraints.gridy++;
			if(currentClass==0) {class1Button.setSelected(true);}
			if(numOfClasses>1) {
				classesPanel.add(class2Panel,classesConstraints);
				classesConstraints.gridy++;
				if(currentClass==1) {class2Button.setSelected(true);}
			}
			if(numOfClasses>2) {
				classesPanel.add(class3Panel,classesConstraints);
				classesConstraints.gridy++;
				if(currentClass==2) {class3Button.setSelected(true);}
			}
			if(numOfClasses>3) {
				classesPanel.add(class4Panel,classesConstraints);
				classesConstraints.gridy++;
				if(currentClass==3) {class4Button.setSelected(true);}
			}
			if(numOfClasses>4) {
				classesPanel.add(class5Panel,classesConstraints);
				classesConstraints.gridy++;
				if(currentClass==4) {class5Button.setSelected(true);}
			}

			// Annotation panel 2
			GridBagLayout annotationLayout2 = new GridBagLayout();
			GridBagConstraints annotationConstraints2 = new GridBagConstraints();
			annotationConstraints2.anchor = GridBagConstraints.NORTHWEST;
			annotationConstraints2.fill = GridBagConstraints.HORIZONTAL;
			annotationConstraints2.gridwidth = 1;
			annotationConstraints2.gridheight = 1;
			annotationConstraints2.gridx = 0;
			annotationConstraints2.gridy = 0;
			annotationPanel2.setLayout(annotationLayout2);

			if(Prefs.getGuiScale()==1.0){
				annotationPanel2.setBorder(BorderFactory.createTitledBorder("Region annotation"));
			}
			else{
				JTextArea annotationPanel2Title = new JTextArea("Region annotation");
				scale(annotationPanel2Title);
				annotationPanel2.add(annotationPanel2Title, annotationConstraints2);
				annotationConstraints2.gridx++;
				JTextArea blankTitle = new JTextArea("");
				scale(blankTitle);
				annotationPanel2.add(blankTitle, annotationConstraints2);
				annotationConstraints2.gridy++;
				annotationConstraints2.gridx=0;
			}
			annotationPanel2.add(newAreaButton, annotationConstraints2);
			annotationConstraints2.gridx++;
			newAreaButton.setSelected(false);
			annotationPanel2.add(removeAreaButton, annotationConstraints2);
			annotationConstraints2.gridy++;
			annotationConstraints2.gridx=0;
			removeAreaButton.setSelected(false);
			annotationPanel2.add(swapAreaClassButton, annotationConstraints2);
			annotationConstraints2.gridy++;
			swapAreaClassButton.setSelected(false);

			// Areas panel
			areaConstraints.anchor = GridBagConstraints.NORTHWEST;
			areaConstraints.fill = GridBagConstraints.HORIZONTAL;
			areaConstraints.gridwidth = 1;
			areaConstraints.gridheight = 1;
			areaConstraints.gridx = 0;
			areaConstraints.gridy = 0;
			areaPanel.setLayout(areaLayout);

			if(Prefs.getGuiScale()==1.0){
				areaPanel.setBorder(BorderFactory.createTitledBorder("Region classes"));
			}
			else{
				JTextArea areaPanelTitle = new JTextArea("Region classes");
				scale(areaPanelTitle);
				areaPanel.add(areaPanelTitle, areaConstraints);
				areaConstraints.gridy++;
			}
			areaPanel.add(filePanel3,areaConstraints);
			areaConstraints.gridy++;
			areaPanel.add(addAreaButton,areaConstraints);
			areaConstraints.gridy++;

			area1Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout area1Layout = new GridBagLayout();
			GridBagConstraints area1Constraints = new GridBagConstraints();
			area1Constraints.anchor = GridBagConstraints.NORTHWEST;
			area1Constraints.fill = GridBagConstraints.HORIZONTAL;
			area1Constraints.gridwidth = 1;
			area1Constraints.gridheight = 1;
			area1Constraints.gridx = 0;
			area1Constraints.gridy = 0;
			area1Panel.setLayout(area1Layout);
			area1Panel.add(area1Button);
			area1Constraints.gridx++;
			area1Panel.add(area1ColorButton);
			area1Constraints.gridx++;
			area1Panel.add(area1RemoveButton);

			area2Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout area2Layout = new GridBagLayout();
			GridBagConstraints area2Constraints = new GridBagConstraints();
			area2Constraints.anchor = GridBagConstraints.NORTHWEST;
			area2Constraints.fill = GridBagConstraints.HORIZONTAL;
			area2Constraints.gridwidth = 1;
			area2Constraints.gridheight = 1;
			area2Constraints.gridx = 0;
			area2Constraints.gridy = 0;
			area2Panel.setLayout(area2Layout);
			area2Panel.add(area2Button);
			area2Constraints.gridx++;
			area2Panel.add(area2ColorButton);
			area2Constraints.gridx++;
			area2Panel.add(area2RemoveButton);

			area3Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout area3Layout = new GridBagLayout();
			GridBagConstraints area3Constraints = new GridBagConstraints();
			area3Constraints.anchor = GridBagConstraints.NORTHWEST;
			area3Constraints.fill = GridBagConstraints.HORIZONTAL;
			area3Constraints.gridwidth = 1;
			area3Constraints.gridheight = 1;
			area3Constraints.gridx = 0;
			area3Constraints.gridy = 0;
			area3Panel.setLayout(area3Layout);
			area3Panel.add(area3Button);
			area3Constraints.gridx++;
			area3Panel.add(area3ColorButton);
			area3Constraints.gridx++;
			area3Panel.add(area3RemoveButton);

			area4Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout area4Layout = new GridBagLayout();
			GridBagConstraints area4Constraints = new GridBagConstraints();
			area4Constraints.anchor = GridBagConstraints.NORTHWEST;
			area4Constraints.fill = GridBagConstraints.HORIZONTAL;
			area4Constraints.gridwidth = 1;
			area4Constraints.gridheight = 1;
			area4Constraints.gridx = 0;
			area4Constraints.gridy = 0;
			area4Panel.setLayout(area4Layout);
			area4Panel.add(area4Button);
			area4Constraints.gridx++;
			area4Panel.add(area4ColorButton);
			area4Constraints.gridx++;
			area4Panel.add(area4RemoveButton);

			area5Panel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout area5Layout = new GridBagLayout();
			GridBagConstraints area5Constraints = new GridBagConstraints();
			area5Constraints.anchor = GridBagConstraints.NORTHWEST;
			area5Constraints.fill = GridBagConstraints.HORIZONTAL;
			area5Constraints.gridwidth = 1;
			area5Constraints.gridheight = 1;
			area5Constraints.gridx = 0;
			area5Constraints.gridy = 0;
			area5Panel.setLayout(area5Layout);
			area5Panel.add(area5Button);
			area5Constraints.gridx++;
			area5Panel.add(area5ColorButton);
			area5Constraints.gridx++;
			area5Panel.add(area5RemoveButton);

			areaPanel.add(area1Panel,areaConstraints);
			areaConstraints.gridy++;
			if(currentArea==0) {area1Button.setSelected(true);}
			if(numOfAreas>1) {
				areaPanel.add(area2Panel,areaConstraints);
				areaConstraints.gridy++;
				if(currentArea==1) {area2Button.setSelected(true);}
			}
			if(numOfAreas>2) {
				areaPanel.add(area3Panel,areaConstraints);
				areaConstraints.gridy++;
				if(currentArea==2) {area3Button.setSelected(true);}
			}
			if(numOfAreas>3) {
				areaPanel.add(area4Panel,areaConstraints);
				areaConstraints.gridy++;
				if(currentArea==3) {area4Button.setSelected(true);}
			}
			if(numOfAreas>4) {
				areaPanel.add(area5Panel,areaConstraints);
				areaConstraints.gridy++;
				if(currentArea==4) {area5Button.setSelected(true);}
			}


			// thresholding marker panel
			JLabel l1,l2;
			l1 = new JLabel("Intensity thresholding");
			scale(l1);
			l2 = new JLabel("Region thresholding");
			scale(l2);
			JPanel thresholdingMarkerPanel = new JPanel(), intensityThresholdingForObjectAssociatedMarkerMarkerPanel = new JPanel(), areaThresholdingMarkerPanel = new JPanel();
			thresholdingMarkerPanel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout thresholdingMarkerPanelLayout = new GridBagLayout();
			GridBagConstraints thresholdingMarkerPanelConstraints = new GridBagConstraints(), intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints = new GridBagConstraints(), areaThresholdingMarkerPanelConstraints = new GridBagConstraints();
			thresholdingMarkerPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			thresholdingMarkerPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			thresholdingMarkerPanelConstraints.gridwidth = 1;
			thresholdingMarkerPanelConstraints.gridheight = 1;
			thresholdingMarkerPanelConstraints.gridx = 0;
			thresholdingMarkerPanelConstraints.gridy = 0;
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.gridwidth = 1;
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.gridheight = 1;
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.gridx = 0;
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.gridy = 0;
			areaThresholdingMarkerPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			areaThresholdingMarkerPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			areaThresholdingMarkerPanelConstraints.gridwidth = 1;
			areaThresholdingMarkerPanelConstraints.gridheight = 1;
			areaThresholdingMarkerPanelConstraints.gridx = 0;
			areaThresholdingMarkerPanelConstraints.gridy = 0;


			thresholdingMarkerPanel.setLayout(thresholdingMarkerPanelLayout);
			thresholdingMarkerPanel.add(l1,thresholdingMarkerPanelConstraints);
			thresholdingMarkerPanelConstraints.gridy++;

			intensityThresholdingForObjectAssociatedMarkerMarkerPanel.add(intensityThresholdingForObjectAssociatedMarkerScrollBar,intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints);
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.gridx++;
			intensityThresholdingForObjectAssociatedMarkerTextArea.setPreferredSize( new Dimension( 50, 24 ) );
			intensityThresholdingForObjectAssociatedMarkerMarkerPanel.add(intensityThresholdingForObjectAssociatedMarkerTextArea,intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints);
			intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints.gridx++;
			intensityThresholdingForObjectAssociatedMarkerMarkerPanel.add(setIntensityThresholdForObjectAssociatedMarkerButton,intensityThresholdingForObjectAssociatedMarkerMarkerPanelConstraints);

			thresholdingMarkerPanel.add(intensityThresholdingForObjectAssociatedMarkerMarkerPanel,thresholdingMarkerPanelConstraints);
			thresholdingMarkerPanelConstraints.gridy++;
			thresholdingMarkerPanel.add(l2,thresholdingMarkerPanelConstraints);
			thresholdingMarkerPanelConstraints.gridy++;

			areaThresholdingMarkerPanel.add(areaThresholdingScrollBar,areaThresholdingMarkerPanelConstraints);
			areaThresholdingMarkerPanelConstraints.gridx++;
			areaThresholdingTextArea.setPreferredSize( new Dimension( 50, 24 ) );
			areaThresholdingMarkerPanel.add(areaThresholdingTextArea,areaThresholdingMarkerPanelConstraints);
			areaThresholdingMarkerPanelConstraints.gridx++;
			areaThresholdingMarkerPanel.add(setAreaThresholdButton,areaThresholdingMarkerPanelConstraints);

			thresholdingMarkerPanel.add(areaThresholdingMarkerPanel,thresholdingMarkerPanelConstraints);
			thresholdingMarkerPanelConstraints.gridy++;

			JPanel acceptanceThresholdingMarkerPanel1 = new JPanel();
			acceptanceThresholdingMarkerPanel1.setBorder(BorderFactory.createTitledBorder(""));
			GridBagConstraints acceptanceThresholdingMarkerPanel1Constraints = new GridBagConstraints();
			acceptanceThresholdingMarkerPanel1Constraints.anchor = GridBagConstraints.NORTHWEST;
			acceptanceThresholdingMarkerPanel1Constraints.fill = GridBagConstraints.HORIZONTAL;
			acceptanceThresholdingMarkerPanel1Constraints.gridwidth = 1;
			acceptanceThresholdingMarkerPanel1Constraints.gridheight = 1;
			acceptanceThresholdingMarkerPanel1Constraints.gridx = 0;
			acceptanceThresholdingMarkerPanel1Constraints.gridy = 0;
			acceptanceThresholdingMarkerPanel1.add(okMarkerForObjectAssociatedMarkersButton,acceptanceThresholdingMarkerPanel1Constraints);
			acceptanceThresholdingMarkerPanel1Constraints.gridx++;
			acceptanceThresholdingMarkerPanel1.add(cancelMarkerForObjectAssociatedMarkersButton,acceptanceThresholdingMarkerPanel1Constraints);
			thresholdingMarkerPanel.add(acceptanceThresholdingMarkerPanel1,thresholdingMarkerPanelConstraints);

			// thresholding marker panel
			JLabel l3;
			l3 = new JLabel("Intensity thresholding");
			scale(l3);
			JPanel thresholdingMarkerPanel2 = new JPanel();
			thresholdingMarkerPanel2.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout thresholdingMarkerPanel2Layout = new GridBagLayout();
			GridBagConstraints thresholdingMarkerPanel2Constraints = new GridBagConstraints();
			thresholdingMarkerPanel2Constraints.anchor = GridBagConstraints.NORTHWEST;
			thresholdingMarkerPanel2Constraints.fill = GridBagConstraints.HORIZONTAL;
			thresholdingMarkerPanel2Constraints.gridwidth = 1;
			thresholdingMarkerPanel2Constraints.gridheight = 1;
			thresholdingMarkerPanel2Constraints.gridx = 0;
			thresholdingMarkerPanel2Constraints.gridy = 0;

			thresholdingMarkerPanel2.setLayout(thresholdingMarkerPanel2Layout);
			thresholdingMarkerPanel2.add(l3,thresholdingMarkerPanel2Constraints);
			thresholdingMarkerPanel2Constraints.gridy++;

			// Top panel
			GridBagLayout topLayout = new GridBagLayout();
			GridBagConstraints topConstraints = new GridBagConstraints();
			topPanel.setLayout(topLayout);
			topConstraints.anchor = GridBagConstraints.NORTHWEST;
			topConstraints.fill = GridBagConstraints.HORIZONTAL;
			topConstraints.gridwidth = 1;
			topConstraints.gridheight = 1;
			topConstraints.gridx = 0;
			topConstraints.gridy = 0;
			topPanel.add(modePanel, topConstraints);
			topConstraints.gridy++;
			topConstraints.insets = new Insets(5, 5, 6, 6);

			// Left panel 1 (including training and options)
			GridBagLayout leftLayout1 = new GridBagLayout();
			GridBagConstraints leftConstraints1 = new GridBagConstraints();
			leftPanel1.setLayout(leftLayout1);
			leftConstraints1.anchor = GridBagConstraints.NORTHWEST;
			leftConstraints1.fill = GridBagConstraints.HORIZONTAL;
			leftConstraints1.gridwidth = 1;
			leftConstraints1.gridheight = 1;
			leftConstraints1.gridx = 0;
			leftConstraints1.gridy = 0;
			leftPanel1.add(annotationPanel1, leftConstraints1);
			leftConstraints1.gridy++;
			leftPanel1.add(classesPanel, leftConstraints1);
			leftConstraints1.gridy++;
			leftPanel1.add(annotationPanel2, leftConstraints1);
			leftConstraints1.gridy++;
			leftPanel1.add(areaPanel, leftConstraints1);
			leftConstraints1.gridy++;
			leftConstraints1.insets = new Insets(5, 5, 6, 6);

			// Left panel 2 (including training and options)
			GridBagLayout leftLayout2 = new GridBagLayout();
			GridBagConstraints leftConstraints2 = new GridBagConstraints();
			leftPanel2.setLayout(leftLayout2);
			leftConstraints2.anchor = GridBagConstraints.NORTHWEST;
			leftConstraints2.fill = GridBagConstraints.HORIZONTAL;
			leftConstraints2.gridwidth = 1;
			leftConstraints2.gridheight = 1;
			leftConstraints2.gridx = 0;
			leftConstraints2.gridy = 0;
			leftPanel2.add(loadImageAndSegmentationPanel, leftConstraints2);
			leftConstraints2.gridy++;
			leftPanel2.add(objectAssociatedMarkersPanel, leftConstraints2);
			leftConstraints2.gridy++;
			leftConstraints2.insets = new Insets(5, 5, 6, 6);

			// Right panel 1
			GridBagLayout rightLayout1 = new GridBagLayout();
			GridBagConstraints rightConstraints1 = new GridBagConstraints();
			rightPanel1.setLayout(rightLayout1);
			rightConstraints1.anchor = GridBagConstraints.NORTHWEST;
			rightConstraints1.fill = GridBagConstraints.HORIZONTAL;
			rightConstraints1.gridwidth = 1;
			rightConstraints1.gridheight = 1;
			rightConstraints1.gridx = 0;
			rightConstraints1.gridy = 0;
			rightPanel1.add(visualizationPanel3, rightConstraints1);
			rightConstraints1.gridy++;
			rightPanel1.add(visualizationPanel1, rightConstraints1);
			rightConstraints1.gridy++;
			rightPanel1.add(analysisPanel1, rightConstraints1);
			rightConstraints1.gridy++;
			rightConstraints1.insets = new Insets(5, 5, 6, 6);

			// Right panel 2
			GridBagLayout rightLayout2 = new GridBagLayout();
			GridBagConstraints rightConstraints2 = new GridBagConstraints();
			rightPanel2.setLayout(rightLayout2);
			rightConstraints2.anchor = GridBagConstraints.NORTHWEST;
			rightConstraints2.fill = GridBagConstraints.HORIZONTAL;
			rightConstraints2.gridwidth = 1;
			rightConstraints2.gridheight = 1;
			rightConstraints2.gridx = 0;
			rightConstraints2.gridy = 0;
			rightPanel2.add(visualizationPanel4, rightConstraints2);
			rightConstraints2.gridy++;
			rightPanel2.add(visualizationPanel2, rightConstraints2);
			rightConstraints2.gridy++;
			rightPanel2.add(analysisPanel2, rightConstraints2);
			rightConstraints2.gridy++;
			rightConstraints2.insets = new Insets(5, 5, 6, 6);

			// Bottom panel 1
			GridBagLayout bottom1Layout = new GridBagLayout();
			GridBagConstraints bottom1Constraints = new GridBagConstraints();
			bottomPanel1.setLayout(bottom1Layout);
			bottom1Constraints.anchor = GridBagConstraints.NORTHWEST;
			bottom1Constraints.fill = GridBagConstraints.HORIZONTAL;
			bottom1Constraints.gridwidth = 1;
			bottom1Constraints.gridheight = 1;
			bottom1Constraints.gridx = 0;
			bottom1Constraints.gridy = 0;
			bottomPanel1.add(thresholdingMarkerPanel, bottom1Constraints);
			bottom1Constraints.gridy++;
			bottomPanel1.add(thresholdingMarkerPanel, bottom1Constraints);
			bottom1Constraints.gridy++;
			bottom1Constraints.insets = new Insets(5, 5, 6, 6);

			GridBagLayout layout = new GridBagLayout();
			GridBagConstraints allConstraints = new GridBagConstraints();
			all.setLayout(layout);

			if(currentMode==0) {
				allConstraints.anchor = GridBagConstraints.NORTHWEST;
				allConstraints.fill = GridBagConstraints.BOTH;

				allConstraints.gridx = 1;
				allConstraints.gridy = 0;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				all.add(topPanel, allConstraints);

				allConstraints.gridx = 0;
				allConstraints.gridy = 1;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				allConstraints.ipadx = 0;
				all.add(leftPanel1, allConstraints);

				allConstraints.gridx = 1;
				allConstraints.gridy = 1;
				allConstraints.weightx = 1;
				allConstraints.weighty = 1;
				all.add(canvas, allConstraints);

				allConstraints.gridx = 2;
				allConstraints.gridy = 1;
				allConstraints.anchor = GridBagConstraints.NORTHEAST;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				all.add(rightPanel1, allConstraints);
			}
			else if(currentMode==1) {
				allConstraints.anchor = GridBagConstraints.NORTHWEST;
				allConstraints.fill = GridBagConstraints.BOTH;

				allConstraints.gridx = 1;
				allConstraints.gridy = 0;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				all.add(topPanel, allConstraints);

				allConstraints.gridx = 0;
				allConstraints.gridy = 1;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				all.add(leftPanel2, allConstraints);

				allConstraints.gridx = 1;
				allConstraints.gridy = 1;
				allConstraints.weightx = 1;
				allConstraints.weighty = 1;
				all.add(canvas, allConstraints);

				allConstraints.gridx = 2;
				allConstraints.gridy = 1;
				allConstraints.anchor = GridBagConstraints.NORTHEAST;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				all.add(rightPanel2, allConstraints);

			}
			else if(currentMode==2) {
				allConstraints.anchor = GridBagConstraints.NORTHWEST;
				allConstraints.fill = GridBagConstraints.BOTH;

				allConstraints.gridx = 0;
				allConstraints.gridy = 1;
				allConstraints.weightx = 1;
				allConstraints.weighty = 1;
				all.add(canvas, allConstraints);

				displayFlag = 0;
				displayImage.setDisplayMode(IJ.GRAYSCALE);
				displayImage.setPosition(chosenChannelForObjectAssociatedMarker, displayImage.getSlice(), displayImage.getFrame());
				displayImage.updateAndDraw();
				IJ.setThreshold(displayImage, 0, intensityThresholdingForObjectAssociatedMarkerScrollBar.getValue(), "Over/Under");
				roiActivationAndDeactivationBasedOnThresholding();
				displayImage.setOverlay(markersOverlay);
				displayImage.updateAndDraw();

				allConstraints.gridx = 0;
				allConstraints.gridy = 2;
				allConstraints.anchor = GridBagConstraints.NORTHEAST;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				all.add(bottomPanel1, allConstraints);
			}

			GridBagLayout wingb = new GridBagLayout();
			GridBagConstraints winc = new GridBagConstraints();
			winc.anchor = GridBagConstraints.NORTHWEST;
			winc.fill = GridBagConstraints.BOTH;
			winc.weightx = 1;
			winc.weighty = 1;
			setLayout(wingb);
			add(all, winc);


			// Remove all key listeners so only the ones useful for the plugin are used
			for (Component p : new Component[]{all, topPanel, leftPanel1, leftPanel2, rightPanel1, rightPanel2}) {
				for (KeyListener kl : getKeyListeners()) {
					p.removeKeyListener(kl);
				}
			}

			addWindowListener(new WindowAdapter() {
				public void windowClosing(WindowEvent e) {
					// cleanup
					exec.shutdownNow();
					imp.getCanvas().removeMouseListener( roiListener );
					imp.getCanvas().removeKeyListener( keyListener );
					objectsAnnotationButton.removeActionListener(listener);
					markerAnnotationButton.removeActionListener(listener);
					loadSegmentationButton.removeActionListener(listener);
					loadObjectAssociatedMarkerButton.removeActionListener(listener);
					loadAreaButton.removeActionListener(listener);
					saveSegmentationButton.removeActionListener(listener);
					saveObjectAssociatedMarkerButton.removeActionListener(listener);
					saveAreaButton.removeActionListener(listener);
					loadImageAndSegmentationButton.removeActionListener(listener);
					analyzeClassesButton.removeActionListener(listener);
					classSnapshotButton.removeActionListener(listener);
					batchClassesMeasurementsButton.removeActionListener(listener);
					analyzeMarkersButton.removeActionListener(listener);
					markerSnapshotButton.removeActionListener(listener);
					batchMarkersButton.removeActionListener(listener);
					newObjectButton.removeActionListener(listener);
					removeObjectButton.removeActionListener(listener);
					splitObjectsButton.removeActionListener(listener);
					mergeObjectsButton.removeActionListener(listener);
					swapObjectClassButton.removeActionListener(listener);
					newAreaButton.removeActionListener(listener);
					removeAreaButton.removeActionListener(listener);
					swapAreaClassButton.removeActionListener(listener);
					addClassButton.removeActionListener(listener);
					class1Button.removeActionListener(listener);
					class1ColorButton.removeActionListener(listener);
					class1RemoveButton.removeActionListener(listener);
					if(numOfClasses>1) {class2Button.removeActionListener(listener);class2ColorButton.removeActionListener(listener);class2RemoveButton.removeActionListener(listener);}
					if(numOfClasses>2) {class3Button.removeActionListener(listener);class3ColorButton.removeActionListener(listener);class3RemoveButton.removeActionListener(listener);}
					if(numOfClasses>3) {class4Button.removeActionListener(listener);class4ColorButton.removeActionListener(listener);class4RemoveButton.removeActionListener(listener);}
					if(numOfClasses>4) {class5Button.removeActionListener(listener);class5ColorButton.removeActionListener(listener);class5RemoveButton.removeActionListener(listener);}
					addObjectAssociatedMarkerButton.removeActionListener(listener);
					addAreaButton.removeActionListener(listener);
					area1Button.removeActionListener(listener);
					area1ColorButton.removeActionListener(listener);
					area1RemoveButton.removeActionListener(listener);
					if(numOfAreas>1) {area2Button.removeActionListener(listener);area2ColorButton.removeActionListener(listener);area2RemoveButton.removeActionListener(listener);}
					if(numOfAreas>2) {area3Button.removeActionListener(listener);area3ColorButton.removeActionListener(listener);area3RemoveButton.removeActionListener(listener);}
					if(numOfAreas>3) {area4Button.removeActionListener(listener);area4ColorButton.removeActionListener(listener);area4RemoveButton.removeActionListener(listener);}
					if(numOfAreas>4) {area5Button.removeActionListener(listener);area5ColorButton.removeActionListener(listener);area5RemoveButton.removeActionListener(listener);}
					visualizeChannel1Button1.removeActionListener(listener);
					visualizeChannel1onlyButton1.removeActionListener(listener);
					visualizeChannel1Button2.removeActionListener(listener);
					visualizeChannel1onlyButton2.removeActionListener(listener);
					visualizeAllChannelsButton1.removeActionListener(listener);
					visualizeAllChannelsButton2.removeActionListener(listener);
					if(numOfObjectAssociatedMarkers>0) {removeMarker1ButtonFromListener();}
					if(numOfObjectAssociatedMarkers>1) {removeMarker2ButtonFromListener();}
					if(numOfObjectAssociatedMarkers>2) {removeMarker3ButtonFromListener();}
					if(numOfObjectAssociatedMarkers>3) {removeMarker4ButtonFromListener();}
					if(numOfObjectAssociatedMarkers>4) {removeMarker5ButtonFromListener();}
					if(numOfObjectAssociatedMarkers>5) {removeMarker6ButtonFromListener();}
					if(numOfObjectAssociatedMarkers>6) {removeMarker7ButtonFromListener();}
					if(numOfChannels>1) {
						visualizeChannel2Button1.removeActionListener(listener);
						visualizeChannel2Button2.removeActionListener(listener);
						visualizeChannel2onlyButton1.removeActionListener(listener);
						visualizeChannel2onlyButton2.removeActionListener(listener);
					}
					if(numOfChannels>2) {
						visualizeChannel3Button1.removeActionListener(listener);
						visualizeChannel3Button2.removeActionListener(listener);
						visualizeChannel3onlyButton1.removeActionListener(listener);
						visualizeChannel3onlyButton2.removeActionListener(listener);
					}
					if(numOfChannels>3) {
						visualizeChannel4Button1.removeActionListener(listener);
						visualizeChannel4Button2.removeActionListener(listener);
						visualizeChannel4onlyButton1.removeActionListener(listener);
						visualizeChannel4onlyButton2.removeActionListener(listener);
					}
					if(numOfChannels>4) {
						visualizeChannel5Button1.removeActionListener(listener);
						visualizeChannel5Button2.removeActionListener(listener);
						visualizeChannel5onlyButton1.removeActionListener(listener);
						visualizeChannel5onlyButton2.removeActionListener(listener);
					}
					if(numOfChannels>5) {
						visualizeChannel6Button1.removeActionListener(listener);
						visualizeChannel6Button2.removeActionListener(listener);
						visualizeChannel6onlyButton1.removeActionListener(listener);
						visualizeChannel6onlyButton2.removeActionListener(listener);
					}
					if(numOfChannels>6) {
						visualizeChannel7Button1.removeActionListener(listener);
						visualizeChannel7Button2.removeActionListener(listener);
						visualizeChannel7onlyButton1.removeActionListener(listener);
						visualizeChannel7onlyButton2.removeActionListener(listener);
					}
					visualizeObjectsButton1.removeActionListener(listener);
					visualizeAreasButton1.removeActionListener(listener);
					visualizeObjectsButton2.removeActionListener(listener);
					visualizeAreasButton2.removeActionListener(listener);
					// Set number of classes back to 1
					numOfClasses = 1;
					on = false;
				}
			});

			canvas.addComponentListener(new ComponentAdapter() {
				public void componentResized(ComponentEvent ce) {
					Rectangle r = canvas.getBounds();
					canvas.setDstDimensions(r.width, r.height);
				}
			});

			imp.getCanvas().addMouseListener( roiListener );
			imp.getCanvas().addKeyListener( keyListener );

			// add listeners
			if(!on) {
				objectsAnnotationButton.addActionListener(listener);
				markerAnnotationButton.addActionListener(listener);
				loadSegmentationButton.addActionListener(listener);
				loadObjectAssociatedMarkerButton.addActionListener(listener);
				loadAreaButton.addActionListener(listener);
				saveSegmentationButton.addActionListener(listener);
				saveObjectAssociatedMarkerButton.addActionListener(listener);
				saveAreaButton.addActionListener(listener);
				loadImageAndSegmentationButton.addActionListener(listener);
				analyzeClassesButton.addActionListener(listener);
				classSnapshotButton.addActionListener(listener);
				batchClassesMeasurementsButton.addActionListener(listener);
				analyzeMarkersButton.addActionListener(listener);
				markerSnapshotButton.addActionListener(listener);
				batchMarkersButton.addActionListener(listener);
				newObjectButton.addActionListener(listener);
				removeObjectButton.addActionListener(listener);
				mergeObjectsButton.addActionListener(listener);
				splitObjectsButton.addActionListener(listener);
				swapObjectClassButton.addActionListener(listener);
				newAreaButton.addActionListener(listener);
				removeAreaButton.addActionListener(listener);
				swapAreaClassButton.addActionListener(listener);
				addClassButton.addActionListener(listener);
				class1Button.addActionListener(listener);
				class1ColorButton.addActionListener(listener);
				class1RemoveButton.addActionListener(listener);
				addObjectAssociatedMarkerButton.addActionListener(listener);
				addAreaButton.addActionListener(listener);
				area1Button.addActionListener(listener);
				area1ColorButton.addActionListener(listener);
				area1RemoveButton.addActionListener(listener);
				visualizeChannel1Button1.addActionListener(listener);
				visualizeChannel1Button2.addActionListener(listener);
				visualizeChannel1onlyButton1.addActionListener(listener);
				visualizeChannel1onlyButton2.addActionListener(listener);
				visualizeAllChannelsButton1.addActionListener(listener);
				visualizeAllChannelsButton2.addActionListener(listener);
				if(numOfChannels>1) {
					visualizeChannel2Button1.addActionListener(listener);
					visualizeChannel2Button2.addActionListener(listener);
					visualizeChannel2onlyButton1.addActionListener(listener);
					visualizeChannel2onlyButton2.addActionListener(listener);
				}
				if(numOfChannels>2) {
					visualizeChannel3Button1.addActionListener(listener);
					visualizeChannel3Button2.addActionListener(listener);
					visualizeChannel3onlyButton1.addActionListener(listener);
					visualizeChannel3onlyButton2.addActionListener(listener);
				}
				if(numOfChannels>3) {
					visualizeChannel4Button1.addActionListener(listener);
					visualizeChannel4Button2.addActionListener(listener);
					visualizeChannel4onlyButton1.addActionListener(listener);
					visualizeChannel4onlyButton2.addActionListener(listener);
				}
				if(numOfChannels>4) {
					visualizeChannel5Button1.addActionListener(listener);
					visualizeChannel5Button2.addActionListener(listener);
					visualizeChannel5onlyButton1.addActionListener(listener);
					visualizeChannel5onlyButton2.addActionListener(listener);
				}
				if(numOfChannels>5) {
					visualizeChannel6Button1.addActionListener(listener);
					visualizeChannel6Button2.addActionListener(listener);
					visualizeChannel6onlyButton1.addActionListener(listener);
					visualizeChannel6onlyButton2.addActionListener(listener);
				}
				if(numOfChannels>6) {
					visualizeChannel7Button1.addActionListener(listener);
					visualizeChannel7Button2.addActionListener(listener);
					visualizeChannel7onlyButton1.addActionListener(listener);
					visualizeChannel7onlyButton2.addActionListener(listener);
				}
				visualizeObjectsButton1.addActionListener(listener);
				visualizeAreasButton1.addActionListener(listener);
				visualizeObjectsButton2.addActionListener(listener);
				visualizeAreasButton2.addActionListener(listener);
				on = true;
			}

		}

		/**
		 * Repaint all panels
		 */
		public void repaintAll()
		{
			this.topPanel.repaint();
			this.leftPanel1.repaint();
			this.leftPanel2.repaint();
			getCanvas().repaint();
			this.rightPanel1.repaint();
			this.rightPanel2.repaint();
			this.all.repaint();
		}

		/**
		 * Find color for area associated markers
		 */
		public byte findAreaColor() {
			byte colorCode = 0;
			boolean foundColor = false;
			while (!foundColor) {
				foundColor = true;
				for(int i=0;i<areaColors.length;i++) {
					if(colorCode==areaColors[i]) {
						colorCode++;
						foundColor = false;
					}
				}
			}
			return colorCode;
		}
		/**
		 * Add new segmentation class (new label and new list on the right side)
		 */
		public byte findClassColor() {
			byte colorCode = 0;
			boolean foundColor = false;
			while (!foundColor) {
				foundColor = true;
				for(int i=0;i<classColors.length;i++) {
					if(colorCode==classColors[i]) {
						colorCode++;
						foundColor = false;
					}
				}
			}
			return colorCode;
		}
		public void addClass()
		{					
			objectsInEachClass[numOfClasses] = new ArrayList<Point[]>();
			if(numOfClasses==1) {
				classesPanel.add(class2Panel,classesConstraints);
				classesConstraints.gridy++;
				class2Button.addActionListener(listener);
				class2ColorButton.addActionListener(listener);
				class2RemoveButton.addActionListener(listener);
				if(classColors[1]==(-1)){classColors[1] = findClassColor();}
				numOfClasses = 2;
			}
			else if(numOfClasses==2) {
				classesPanel.add(class3Panel,classesConstraints);
				classesConstraints.gridy++;
				class3Button.addActionListener(listener);
				class3ColorButton.addActionListener(listener);
				class3RemoveButton.addActionListener(listener);
				if(classColors[2]==(-1)){classColors[2] = findClassColor();}
				numOfClasses = 3;
			}
			else if(numOfClasses==3) {
				classesPanel.add(class4Panel,classesConstraints);
				classesConstraints.gridy++;
				class4Button.addActionListener(listener);
				class4ColorButton.addActionListener(listener);
				class4RemoveButton.addActionListener(listener);
				if(classColors[3]==(-1)){classColors[3] = findClassColor();}
				numOfClasses = 4;
			}
			else if(numOfClasses==4) {
				classesPanel.add(class5Panel,classesConstraints);
				classesConstraints.gridy++;
				class5Button.addActionListener(listener);
				class5ColorButton.addActionListener(listener);
				class5RemoveButton.addActionListener(listener);
				if(classColors[4]==(-1)){classColors[4] = findClassColor();}
				numOfClasses = 5;
			}
			repaintAll();
		}
		/**
		 * Add new area
		 */
		public void addAreaClass()
		{					
			areasInEachClass[numOfAreas] = new ArrayList<Point[]>();
			if(numOfAreas==1) {
				areaPanel.add(area2Panel,areaConstraints);
				areaConstraints.gridy++;
				area2Button.addActionListener(listener);
				area2ColorButton.addActionListener(listener);
				area2RemoveButton.addActionListener(listener);
				if(areaColors[1]==(-1)){areaColors[1] = findAreaColor();}
				numOfAreas = 2;
			}
			else if(numOfAreas==2) {
				areaPanel.add(area3Panel,areaConstraints);
				areaConstraints.gridy++;
				area3Button.addActionListener(listener);
				area3ColorButton.addActionListener(listener);
				area3RemoveButton.addActionListener(listener);
				if(areaColors[2]==(-1)){areaColors[2] = findAreaColor();}
				numOfAreas = 3;
			}
			else if(numOfAreas==3) {
				areaPanel.add(area4Panel,areaConstraints);
				areaConstraints.gridy++;
				area4Button.addActionListener(listener);
				area4ColorButton.addActionListener(listener);
				area4RemoveButton.addActionListener(listener);
				if(areaColors[3]==(-1)){areaColors[3] = findAreaColor();}
				numOfAreas = 4;
			}
			else if(numOfAreas==4) {
				areaPanel.add(area5Panel,areaConstraints);
				areaConstraints.gridy++;
				area5Button.addActionListener(listener);
				area5ColorButton.addActionListener(listener);
				area5RemoveButton.addActionListener(listener);
				if(areaColors[4]==(-1)){areaColors[4] = findAreaColor();}
				numOfAreas = 5;
			}
			repaintAll();
		}

		/**
		 * Add new marker
		 */
		public void addMarker()
		{	
			for(int j=0;j<4;j++) {
				positiveNucleiForEachMarker[numOfObjectAssociatedMarkers][j] = new ArrayList<Short>();
			}
			positivelyLabelledNucleiForEachMarker[numOfObjectAssociatedMarkers] = new ArrayList<Short>();
			negativelyLabelledNucleiForEachMarker[numOfObjectAssociatedMarkers] = new ArrayList<Short>();
			featuresForEachMarker[numOfObjectAssociatedMarkers] = new ArrayList<double[]>();
			if(numOfObjectAssociatedMarkers==0) {
				objectAssociatedMarkersPanel.add(marker1PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				objectAssociatedMarkersPanel.add(marker1PatternPanel2, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				addMarker1ButtonFromListener();
				numOfObjectAssociatedMarkers = 1;
			}
			else if(numOfObjectAssociatedMarkers==1) {
				objectAssociatedMarkersPanel.add(marker2PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				objectAssociatedMarkersPanel.add(marker2PatternPanel2, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				addMarker2ButtonFromListener();
				numOfObjectAssociatedMarkers = 2;
			}
			else if(numOfObjectAssociatedMarkers==2) {
				objectAssociatedMarkersPanel.add(marker3PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				objectAssociatedMarkersPanel.add(marker3PatternPanel2, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				addMarker3ButtonFromListener();
				numOfObjectAssociatedMarkers = 3;
			}
			else if(numOfObjectAssociatedMarkers==3) {
				objectAssociatedMarkersPanel.add(marker4PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				objectAssociatedMarkersPanel.add(marker4PatternPanel2, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				addMarker4ButtonFromListener();
				numOfObjectAssociatedMarkers = 4;
			}
			else if(numOfObjectAssociatedMarkers==4) {
				objectAssociatedMarkersPanel.add(marker5PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				objectAssociatedMarkersPanel.add(marker5PatternPanel2, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				addMarker5ButtonFromListener();
				numOfObjectAssociatedMarkers = 5;
			}
			else if(numOfObjectAssociatedMarkers==5) {
				objectAssociatedMarkersPanel.add(marker6PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				objectAssociatedMarkersPanel.add(marker6PatternPanel2, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				addMarker6ButtonFromListener();
				numOfObjectAssociatedMarkers = 6;
			}
			else if(numOfObjectAssociatedMarkers==6) {
				objectAssociatedMarkersPanel.add(marker7PatternPanel1, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				objectAssociatedMarkersPanel.add(marker7PatternPanel2, objectAssociatedMarkersConstraints);
				objectAssociatedMarkersConstraints.gridy++;
				addMarker7ButtonFromListener();
				numOfObjectAssociatedMarkers = 7;
			}

			repaintAll();
		}
	}

	/**
	 * Compute intensity threshold for which the objects become positive
	 */
	void computeIntensityThresholdForEachObject(List<Polygon> [] cellCompartmentObjectsInEachClass) {
		int maxObjectsForOneClass=0;
		for(int c=0;c<numOfClasses;c++) {
			if(cellCompartmentObjectsInEachClass[c].size()>maxObjectsForOneClass) {
				maxObjectsForOneClass = cellCompartmentObjectsInEachClass[c].size(); 
			}
		}
		intensityThresholdsForObjectAssociatedMarkers = new short[numOfClasses][maxObjectsForOneClass];
		ImageProcessor ipt = displayImage.getStack().getProcessor(chosenChannelForObjectAssociatedMarker);
		
		for(int c=0;c<numOfClasses;c++) {
			for(int i=0;i<cellCompartmentObjectsInEachClass[c].size();i++) {
				Polygon fp = cellCompartmentObjectsInEachClass[c].get(i);
				if(fp.npoints>0) {
					short[] intensities = new short[fp.npoints];
					for(int p=0;p<fp.npoints;p++) {
						intensities[p] = (short)ipt.getf(fp.xpoints[p],fp.ypoints[p]);
					}
					Arrays.sort(intensities);
					int currentThreshold = (int)((float)fp.npoints - (float)areaThresholdingScrollBar.getValue()*(float)fp.npoints/(float)100);
					if(currentThreshold>=fp.npoints) {currentThreshold = fp.npoints-1;}
					if(currentThreshold<0) {currentThreshold = 0;}
					intensityThresholdsForObjectAssociatedMarkers[c][i] = intensities[currentThreshold];
				}
				else {
					intensityThresholdsForObjectAssociatedMarkers[c][i] = 0;
				}
			}
		}
	}
	/**
	 * Add objects defined by the user as ROIs
	 */
	private void addObject()
	{
		// get selected roi
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		// update flags for cell compartment computation
		nuclearComponentFlag = false;
		innerNuclearComponentFlag = false;
		membranarComponentFlag = false;
		cytoplasmicComponentFlag = false;
		rt_nuclearML_flag = false;
		
		// remove roi
		displayImage.killRoi();

		// count points in the roi that do not overlap with previous rois
		Point[] pts = r.getContainedPoints();
		int nbPts=0;
		for (int u=0; u<pts.length; u++) {
			if(roiFlag[pts[u].x][pts[u].y][0]==(-1)) {
				nbPts++;
			}
		}
		// make sure that the new nucleus is defined by at least one point
		if(nbPts>3) {
			// define points in the roi that do not overlap with previous rois 
			int[] xPoints = new int[nbPts];
			int[] yPoints = new int[nbPts];
			nbPts=0;
			for (int u=0; u<pts.length; u++) {
				if(roiFlag[pts[u].x][pts[u].y][0]==(-1)) {
					xPoints[nbPts] = pts[u].x;
					yPoints[nbPts] = pts[u].y;
					nbPts++;
				}
			}

			// displaying
			if(nbPts==pts.length) {
				// if the new roi does not overlap with previous rois -> extract current roi as outline
				drawNewObjectContour(r,currentClass);
				Point[] RoiPoints = new Point[xPoints.length];
				for(int u = 0; u< xPoints.length; u++) {
					roiFlag[xPoints[u]][yPoints[u]][0] = currentClass;
					roiFlag[xPoints[u]][yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
					roiFlag[xPoints[u]][yPoints[u]][2] = (short)(overlay.size()-1);
					RoiPoints[u] = new Point(xPoints[u],yPoints[u]);
				}
				// define polygon and roi corresponding to the new region
				//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,nbPts,Roi.FREEROI);
				// save new nucleus as roi in the corresponding class
				objectsInEachClass[currentClass].add(RoiPoints);
			}
			else {
				// extract non overlapping nucleus
				drawNewObjectContour(xPoints,yPoints,currentClass);
				// add nucleus to the list of nuclei
				Point[] RoiPoints = new Point[xPoints.length];
				for(int u = 0; u< xPoints.length; u++) {
					roiFlag[xPoints[u]][yPoints[u]][0] = currentClass;
					roiFlag[xPoints[u]][yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
					roiFlag[xPoints[u]][yPoints[u]][2] = (short)(overlay.size()-1);
					RoiPoints[u] = new Point(xPoints[u],yPoints[u]);
				}
				// save new nucleus as roi in the corresponding class
				objectsInEachClass[currentClass].add(RoiPoints);
			}
		}
		// refresh displaying
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();
	}
	/**
	 * Add objects defined by the user as ROIs
	 */
	private void addArea()
	{
		// get selected roi
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		// remove roi
		displayImage.killRoi();

		// count points in the roi that do not overlap with previous rois
		Point[] pts = r.getContainedPoints();
		int nbPts=0;
		for (int u=0; u<pts.length; u++) {
			if(areaFlag[pts[u].x][pts[u].y][0]==(-1)) {
				nbPts++;
			}
		}
		// make sure that the new nucleus is defined by at least one point
		if(nbPts>3) {
			// define points in the roi that do not overlap with previous rois 
			int[] xPoints = new int[nbPts];
			int[] yPoints = new int[nbPts];
			nbPts=0;
			for (int u=0; u<pts.length; u++) {
				if(areaFlag[pts[u].x][pts[u].y][0]==(-1)) {
					xPoints[nbPts] = pts[u].x;
					yPoints[nbPts] = pts[u].y;
					nbPts++;
				}
			}

			// if the new roi does not overlap with previous rois -> extract current roi as outline
			Point[] RoiPoints = new Point[xPoints.length];
			for(int u = 0; u< xPoints.length; u++) {
				areaFlag[xPoints[u]][yPoints[u]][0] = currentArea;
				areaFlag[xPoints[u]][yPoints[u]][1] = (short)areasInEachClass[currentArea].size();
				areaFlag[xPoints[u]][yPoints[u]][2] = (short)(overlay.size());
				RoiPoints[u] = new Point(xPoints[u],yPoints[u]);
			}
			// define polygon and roi corresponding to the new region
			//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,nbPts,Roi.FREEROI);
			// save new nucleus as roi in the corresponding class
			drawArea(RoiPoints,currentArea);
			areasInEachClass[currentArea].add(RoiPoints);
		}
		// refresh displaying
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();
	}
	/** remove all markers from markers overlay */
	void removeMarkersFromOverlay() {
		if(currentObjectAssociatedMarker>(-1)) {
			if(methodToIdentifyObjectAssociatedMarkers[currentObjectAssociatedMarker]==2){
				// remove ML labelled nuclei
				for(int i = 0; i < positivelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].size(); i++) {
					Point[] pts = overlay.get(positivelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].get(i)).getContainedPoints();
					int currentX=-1,currentY=-1;
					if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
						currentX = pts[pts.length/2].x;
						currentY = pts[pts.length/2].y;
					}
					else {
						for(int k = 0; k < pts.length; k++) {
							if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
								currentX = pts[k].x;
								currentY = pts[k].y;
							}
						}
					}
					if(currentX>(-1)) {
						if(roiFlag[currentX][currentY][2]>(-1)) {
							if(roiFlag[currentX][pts[pts.length/2].y][2]>(-1)) {
								markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeColor(colors[classColors[roiFlag[currentX][currentY][0]]]);
								markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeWidth(0);
							}
						}
					}
				}
				for(int i = 0; i < negativelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].size(); i++) {
					Point[] pts = overlay.get(negativelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].get(i)).getContainedPoints();
					int currentX=-1,currentY=-1;
					if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
						currentX = pts[pts.length/2].x;
						currentY = pts[pts.length/2].y;
					}
					else {
						for(int k = 0; k < pts.length; k++) {
							if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
								currentX = pts[k].x;
								currentY = pts[k].y;
							}
						}
					}
					if(currentX>(-1)) {
						if(roiFlag[currentX][currentY][2]>(-1)) {
							if(roiFlag[currentX][pts[pts.length/2].y][2]>(-1)) {
								markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeColor(colors[classColors[roiFlag[currentX][currentY][0]]]);
								markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeWidth(0);
							}
						}
					}
				}
			}
			for(int p = 0; p < 4; p++) {
				for(int i = 0; i < positiveNucleiForEachMarker[currentObjectAssociatedMarker][p].size(); i++) {
					Point[] pts = overlay.get(positiveNucleiForEachMarker[currentObjectAssociatedMarker][p].get(i)).getContainedPoints();
					int currentX=-1,currentY=-1;
					if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
						currentX = pts[pts.length/2].x;
						currentY = pts[pts.length/2].y;
					}
					else {
						for(int k = 0; k < pts.length; k++) {
							if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
								currentX = pts[k].x;
								currentY = pts[k].y;
							}
						}
					}
					if(currentX>(-1)) {
						if(roiFlag[currentX][currentY][2]>(-1)) {
							if(roiFlag[currentX][pts[pts.length/2].y][2]>(-1)) {
								markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeColor(colors[classColors[roiFlag[currentX][currentY][0]]]);
								markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeWidth(0);
							}
						}
					}
				}
			}
		}
		displayImage.updateAndDraw();
	}
	/** activate/deactivate rois for marker identification based on thresholding */
	void roiActivationAndDeactivationBasedOnThresholding() {
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				if(intensityThresholdingForObjectAssociatedMarkerScrollBar.getValue()<intensityThresholdsForObjectAssociatedMarkers[i][j]) {
					Point[] pl = objectsInEachClass[i].get(j);
					Point pt = new Point(pl[pl.length/2].x,pl[pl.length/2].y);
					activateNucleusMarkerThresholding(pt);
				}
				else {
					Point[] pl = objectsInEachClass[i].get(j);
					Point pt = new Point(pl[pl.length/2].x,pl[pl.length/2].y);
					deactivateNucleusMarkerThresholding(pt);
				}
			}
		}
	}
	/** compute nuclear component array */
	void computeNuclearComponent(){
		IJ.run("Conversions...", " ");
		nuclearComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		int[][][] nuclei = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				Point[] fp = objectsInEachClass[i].get(j);
				for(int k=0;k<fp.length;k++) {
					nuclei[i][fp[k].x][fp[k].y] = j+1;
					nuclearComponent[i][fp[k].x][fp[k].y] = j+1;
				}
			}
		}
		for(int y=0;y<displayImage.getHeight();y++) {
			for(int x=0;x<displayImage.getWidth();x++) {
				boolean nucleusSite=false;				
				for(int i=0;i<numOfClasses;i++) {
					if(nuclei[i][x][y]>0) {
						nucleusSite = true;
					}
					if(nucleusSite) {
						boolean remove=false;
						for(int u=-1;u<=1;u++) {
							if(((x+u)>=0)&&((x+u)<displayImage.getWidth())) {
								for(int v=-1;v<=1;v++) {
									if(((y+v)>=0)&&((y+v)<displayImage.getHeight())) {
										if((nuclei[i][x+u][y+v]==0)||(nuclei[i][x+u][y+v]!=nuclei[i][x][y])) {
											remove = true;
										}
									}
								}
							}
						}
						if(remove) {
							nuclearComponent[i][x][y] = 0;
						}
					}
				}
			}
		}
		IJ.run("Conversions...", "scale");
	}
	/** compute inner nuclear component array */
	void computeInnerNuclearComponent(){
		innerNuclearComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<numOfClasses;i++) {
			//int globalIndex = 0, cpt=0;
			//while(globalIndex<objectsInEachClass[i].size()) {
			int[][] currentNuclei = new int[displayImage.getWidth()][displayImage.getHeight()];
			int[][] erodedNuclei = new int[displayImage.getWidth()][displayImage.getHeight()];
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				Point[] fp = objectsInEachClass[i].get(j);
				for(int k=0;k<fp.length;k++) {
					currentNuclei[fp[k].x][fp[k].y] = j+1;
				}
			}
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					if(currentNuclei[x][y]>0){
						boolean zeroNeighbor = false;
						for(int v=-1;v<=1;v++) {
							if((y+v>=0)&&((y+v)<displayImage.getHeight())){
								for(int u=-1;u<=1;u++) {
									if((x+u>=0)&&((x+u)<displayImage.getWidth())){
										if((currentNuclei[x+u][y+v]==0)||(currentNuclei[x+u][y+v]!=currentNuclei[x][y])){
											zeroNeighbor = true;
										}
									}
								}
							}
						}
						if(!zeroNeighbor){
							erodedNuclei[x][y] = currentNuclei[x][y];
						}
					}
				}
			}
			ImageProcessor erodedNucleiIP = new FloatProcessor(erodedNuclei);
			ImagePlus erodedNucleiImage = new ImagePlus("Erosion, radius = 1", erodedNucleiIP);
			IJ.run(erodedNucleiImage, "Minimum...", "radius=1");
			ImageProcessor erodedNuclei2Ip = erodedNucleiImage.getStack().getProcessor(1);
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					innerNuclearComponent[i][x][y] = (int)erodedNuclei2Ip.getf(x,y);
				}
			}
		}
	}
	/** compute membranar component */
	void computeMembranarComponent(){
		membranarComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<numOfClasses;i++) {
			int[][] currentNuclei = new int[displayImage.getWidth()][displayImage.getHeight()];
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				Point[] fp = objectsInEachClass[i].get(j);
				for(int k=0;k<fp.length;k++) {
					currentNuclei[fp[k].x][fp[k].y] = j+1;
				}
			}
			ImageProcessor nucleiIP = new FloatProcessor(currentNuclei);
			ImagePlus nucleiImage = new ImagePlus("Voronoi 3D, radius = " + 3, nucleiIP);
			IJ.run(nucleiImage, "3D Watershed Voronoi", "radius_max=" + 3);
			IJ.selectWindow("VoronoiZones");
			ImagePlus nucleiImagevoronoi3D = IJ.getImage();
			IJ.doCommand("Close");
			ImageProcessor nucleiImagevoronoi3DIp = nucleiImagevoronoi3D.getStack().getProcessor(1);
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					if(innerNuclearComponent[i][x][y]==0){
						membranarComponent[i][x][y] = (int)nucleiImagevoronoi3DIp.getf(x,y);
					}
				}
			}
		}
	}
	/** compute cytoplasmic component */
	void computeCytoplasmicComponent(){
		cytoplasmicComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<numOfClasses;i++) {
			int[][] currentNuclei = new int[displayImage.getWidth()][displayImage.getHeight()];
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				Point[] fp = objectsInEachClass[i].get(j);
				for(int k=0;k<fp.length;k++) {
					currentNuclei[fp[k].x][fp[k].y] = j+1;
				}
			}
			ImageProcessor nucleiIP = new FloatProcessor(currentNuclei);
			ImagePlus nucleiImage = new ImagePlus("Voronoi 3D, radius = " + 5, nucleiIP);
			IJ.run(nucleiImage, "3D Watershed Voronoi", "radius_max=" + 5);
			IJ.selectWindow("VoronoiZones");
			ImagePlus nucleiImagevoronoi3D = IJ.getImage();
			IJ.doCommand("Close");
			ImageProcessor nucleiImagevoronoi3DIp = nucleiImagevoronoi3D.getStack().getProcessor(1);
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					if(innerNuclearComponent[i][x][y]==0){
						cytoplasmicComponent[i][x][y] = (int)nucleiImagevoronoi3DIp.getf(x,y);
					}
				}
			}
		}
	}
	/** compute cell component */
	int[][][] computeCellComponent(){
		int[][][] cellComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<numOfClasses;i++) {
			int[][] currentNuclei = new int[displayImage.getWidth()][displayImage.getHeight()];
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				Point[] fp = objectsInEachClass[i].get(j);
				for(int k=0;k<fp.length;k++) {
					currentNuclei[fp[k].x][fp[k].y] = j+1;
				}
			}
			ImageProcessor nucleiIP = new FloatProcessor(currentNuclei);
			ImagePlus nucleiImage = new ImagePlus("Voronoi 3D, radius = " + 5, nucleiIP);
			IJ.run(nucleiImage, "3D Watershed Voronoi", "radius_max=" + 5);
			IJ.selectWindow("VoronoiZones");
			ImagePlus nucleiImagevoronoi3D = IJ.getImage();
			IJ.doCommand("Close");
			ImageProcessor nucleiImagevoronoi3DIp = nucleiImagevoronoi3D.getStack().getProcessor(1);
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					cellComponent[i][x][y] = (int)nucleiImagevoronoi3DIp.getf(x,y);
				}
			}
		}
		return cellComponent;
	}
	/** process to define thresholded markers */ 
	private boolean addObjectAssociatedMarkerWindow()
	{
		removeMarkersFromOverlay();
		
		/** buttons for marker characterization */
		JRadioButton nuclearRadioButton = new JRadioButton("Nuclear marker");
		scale(nuclearRadioButton);
		nuclearRadioButton.setSelected(true);
		JRadioButton membranarRadioButton = new JRadioButton("Nuclear membrane marker");
		scale(membranarRadioButton);
		membranarRadioButton.setSelected(false);
		JRadioButton cytoplasmicRadioButton = new JRadioButton("Cytoplasmic marker");
		scale(cytoplasmicRadioButton);
		cytoplasmicRadioButton.setSelected(false);
		
		ButtonGroup bg1=new ButtonGroup();    
		bg1.add(nuclearRadioButton);
		bg1.add(membranarRadioButton);
		bg1.add(cytoplasmicRadioButton);

		JPanel markerTypePanel = new JPanel();
		markerTypePanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout markerTypePanelLayout = new GridBagLayout();
		
		GridBagConstraints markerTypePanelConstraints = new GridBagConstraints();
		markerTypePanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		markerTypePanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		markerTypePanelConstraints.gridwidth = 1;
		markerTypePanelConstraints.gridheight = 1;
		markerTypePanelConstraints.gridx = 0;
		markerTypePanelConstraints.gridy = 0;
		markerTypePanel.setLayout(markerTypePanelLayout);
		markerTypePanel.add(nuclearRadioButton,markerTypePanelConstraints);
		markerTypePanelConstraints.gridy++;
		markerTypePanel.add(membranarRadioButton,markerTypePanelConstraints);
		markerTypePanelConstraints.gridy++;
		markerTypePanel.add(cytoplasmicRadioButton,markerTypePanelConstraints);

		GenericDialogPlus gd1 = new GenericDialogPlus("Marker creation");
		gd1.addMessage("What is the type of the marker?");
		
		gd1.addComponent(markerTypePanel);
		gd1.showDialog();

		if (gd1.wasCanceled())
			return false;

		// update cell compartment marker status
		if(nuclearRadioButton.isSelected()) {
			markerCellcompartment[numOfObjectAssociatedMarkers-1] = 0;
		}
		else if(membranarRadioButton.isSelected()) {
			markerCellcompartment[numOfObjectAssociatedMarkers-1] = 1;
		}
		else if(cytoplasmicRadioButton.isSelected()) {
			markerCellcompartment[numOfObjectAssociatedMarkers-1] = 2;
		}

		/** buttons for thresholding decision */
		JRadioButton manualAnnotationRadioButton = new JRadioButton("Manual annotation");
		scale(manualAnnotationRadioButton);
		manualAnnotationRadioButton.setSelected(true);
		JRadioButton thresholdingRadioButton = new JRadioButton("Thresholding");
		scale(thresholdingRadioButton);
		thresholdingRadioButton.setSelected(false);
		JRadioButton regressionRadioButton = new JRadioButton("Machine learning");
		scale(regressionRadioButton);
		regressionRadioButton.setSelected(false);

		JPanel identificationMethodPanel = new JPanel();
		identificationMethodPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout identificationMethodPanelLayout = new GridBagLayout();
		GridBagConstraints identificationMethodPanelConstraints = new GridBagConstraints();
		identificationMethodPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		identificationMethodPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		identificationMethodPanelConstraints.gridwidth = 1;
		identificationMethodPanelConstraints.gridheight = 1;
		identificationMethodPanelConstraints.gridx = 0;
		identificationMethodPanelConstraints.gridy = 0;
		identificationMethodPanel.setLayout(identificationMethodPanelLayout);
		identificationMethodPanel.add(manualAnnotationRadioButton,identificationMethodPanelConstraints);
		identificationMethodPanelConstraints.gridy++;
		identificationMethodPanel.add(thresholdingRadioButton,identificationMethodPanelConstraints);
		identificationMethodPanelConstraints.gridy++;
		identificationMethodPanel.add(regressionRadioButton,identificationMethodPanelConstraints);

		ButtonGroup bg2=new ButtonGroup();    
		bg2.add(manualAnnotationRadioButton);
		bg2.add(thresholdingRadioButton);
		bg2.add(regressionRadioButton);

		GenericDialogPlus gd2 = new GenericDialogPlus("Marker identification method");
		gd2.addMessage("Which method do you want to use to identify markers associated with objects?");
		gd2.addComponent(identificationMethodPanel);
		gd2.showDialog();

		if (gd2.wasCanceled())
			return false;

		if(manualAnnotationRadioButton.isSelected()){
			methodToIdentifyObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1] = 0;
			updateAnnotateObjectAssociatedMarker(numOfObjectAssociatedMarkers-1,false);
		}
		if(thresholdingRadioButton.isSelected()) {
			methodToIdentifyObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1] = 1;
			visualizeObjectsButton2.setSelected(false);
			removeObjectsFromOverlay();
			
			/** buttons for thresholding decision */
			JRadioButton channel1RadioButton = new JRadioButton("Channel 1");
			scale(channel1RadioButton);
			channel1RadioButton.setSelected(true);
			JRadioButton channel2RadioButton = new JRadioButton("Channel 2");
			scale(channel2RadioButton);
			channel2RadioButton.setSelected(false);
			JRadioButton channel3RadioButton = new JRadioButton("Channel 3");
			scale(channel3RadioButton);
			channel3RadioButton.setSelected(false);
			JRadioButton channel4RadioButton = new JRadioButton("Channel 4");
			scale(channel4RadioButton);
			channel4RadioButton.setSelected(false);
			JRadioButton channel5RadioButton = new JRadioButton("Channel 5");
			scale(channel5RadioButton);
			channel5RadioButton.setSelected(false);
			JRadioButton channel6RadioButton = new JRadioButton("Channel 6");
			scale(channel6RadioButton);
			channel6RadioButton.setSelected(false);
			JRadioButton channel7RadioButton = new JRadioButton("Channel 7");
			scale(channel7RadioButton);
			channel7RadioButton.setSelected(false);

			JPanel currentchannelPanel = new JPanel();
			currentchannelPanel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout currentchannelPanelLayout = new GridBagLayout();
			GridBagConstraints currentchannelPanelConstraints = new GridBagConstraints();
			currentchannelPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			currentchannelPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			currentchannelPanelConstraints.gridwidth = 1;
			currentchannelPanelConstraints.gridheight = 1;
			currentchannelPanelConstraints.gridx = 0;
			currentchannelPanelConstraints.gridy = 0;
			currentchannelPanel.setLayout(currentchannelPanelLayout);
			currentchannelPanel.add(channel1RadioButton,currentchannelPanelConstraints);
			currentchannelPanelConstraints.gridy++;
			if(numOfChannels>1) {
				currentchannelPanel.add(channel2RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>2) {
				currentchannelPanel.add(channel3RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>3) {
				currentchannelPanel.add(channel4RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>4) {
				currentchannelPanel.add(channel5RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>5) {
				currentchannelPanel.add(channel6RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>6) {
				currentchannelPanel.add(channel7RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			ButtonGroup bg3=new ButtonGroup();
			switch (numOfChannels) {
			case 1:
				bg3.add(channel1RadioButton);				
				break;
			case 2:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);
				break;
			case 3:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);
				break;
			case 4:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);
				break;
			case 5:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);bg3.add(channel5RadioButton);
				break;
			case 6:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);bg3.add(channel5RadioButton);bg3.add(channel6RadioButton);
				break;
			case 7:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);bg3.add(channel5RadioButton);bg3.add(channel6RadioButton);bg3.add(channel7RadioButton);
				break;
			default:
				break;
			}


			GenericDialogPlus gd3 = new GenericDialogPlus("Channel associated with the marker");
			gd3.addMessage("Which channel is associated with this marker?");
			gd3.addComponent(currentchannelPanel);
			gd3.showDialog();

			if (gd3.wasCanceled())
				return false;

			chosenChannelForObjectAssociatedMarker = 1;
			if(channel2RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker= 2;}
			else if(channel3RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 3;}
			else if(channel4RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 4;}
			else if(channel5RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 5;}
			else if(channel6RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 6;}
			else if(channel7RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 7;}
			channelsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1] = chosenChannelForObjectAssociatedMarker;

			currentMode = 2;
			currentObjectAssociatedMarker = numOfObjectAssociatedMarkers-1;
			currentPattern = 0;

			List<Polygon> [] cellComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];
			for(int i=0;i<numOfClasses;i++) {
				cellComponentInEachClass[i] = new ArrayList<Polygon>();
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Polygon fp = new Polygon();
					cellComponentInEachClass[i].add(fp);
				}
			}

			if(nuclearRadioButton.isSelected()) {
				if(!nuclearComponentFlag){
					computeNuclearComponent();
					nuclearComponentFlag = true;
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(nuclearComponent[i][x][y]>0) {
								cellComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
			}
			else if(membranarRadioButton.isSelected()) {
				if(!nuclearComponentFlag){
					computeNuclearComponent();
					nuclearComponentFlag = true;
				}
				if(!innerNuclearComponentFlag){
					computeInnerNuclearComponent();
					innerNuclearComponentFlag = true;
				}
				if(!membranarComponentFlag){
					computeMembranarComponent();
					membranarComponentFlag = true;
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								cellComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
			}
			else if(cytoplasmicRadioButton.isSelected()) {
				if(!nuclearComponentFlag){
					computeNuclearComponent();
					nuclearComponentFlag = true;
				}
				if(!innerNuclearComponentFlag){
					computeInnerNuclearComponent();
					innerNuclearComponentFlag = true;
				}
				if(!cytoplasmicComponentFlag){
					computeCytoplasmicComponent();
					cytoplasmicComponentFlag = true;
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cellComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
			}
			ImageProcessor ipt = displayImage.getStack().getProcessor(chosenChannelForObjectAssociatedMarker);
			int maxIntensity=0;
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					int value = (int)ipt.getf(x,y);
					if(value>maxIntensity) {maxIntensity = value;}
				}
			}

			intensityThresholdingForObjectAssociatedMarkerScrollBar.setMaximum(maxIntensity);
			intensityThresholdingForObjectAssociatedMarkerScrollBar.setValue(maxIntensity/2);
			intensityThresholdingForObjectAssociatedMarkerTextArea.setText("" + maxIntensity/2);
			intensityThresholdingForObjectAssociatedMarkerTextArea.setEditable(false);
			thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1][1] = maxIntensity/2;
			computeIntensityThresholdForEachObject(cellComponentInEachClass);
			areaThresholdingScrollBar.setValue(35);
			areaThresholdingTextArea.setText("" + 35);
			areaThresholdingTextArea.setEditable(false);
			thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1][0] = 35;
			intensityThresholdingForObjectAssociatedMarkerScrollBar.addChangeListener(new ChangeListener() {

				@Override
				public void stateChanged(ChangeEvent ce) {
					IJ.setThreshold(displayImage, 0, ((JSlider) ce.getSource()).getValue(), "Over/Under");
					roiActivationAndDeactivationBasedOnThresholding();
					intensityThresholdingForObjectAssociatedMarkerTextArea.setText("" + ((JSlider) ce.getSource()).getValue());
					thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1][1] = intensityThresholdingForObjectAssociatedMarkerScrollBar.getValue();
				}
			});
			areaThresholdingScrollBar.addChangeListener(new ChangeListener() {

				@Override
				public void stateChanged(ChangeEvent arg0) {
					computeIntensityThresholdForEachObject(cellComponentInEachClass);
					roiActivationAndDeactivationBasedOnThresholding();
					areaThresholdingTextArea.setText("" + ((JSlider) arg0.getSource()).getValue());
					thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1][0] = areaThresholdingScrollBar.getValue(); 
					displayImage.updateAndDraw();
				}
			});

			okMarkerForObjectAssociatedMarkersButton.addActionListener(listener);
			cancelMarkerForObjectAssociatedMarkersButton.addActionListener(listener);
			setIntensityThresholdForObjectAssociatedMarkerButton.addActionListener(listener);
			setAreaThresholdButton.addActionListener(listener);
			updateAnnotateObjectAssociatedMarker(numOfObjectAssociatedMarkers-1,true);
			repaintWindow();
		}
		if(regressionRadioButton.isSelected()) {
			methodToIdentifyObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1] = 2;
			
			/** buttons for thresholding decision */
			JRadioButton channel1RadioButton = new JRadioButton("Channel 1");
			scale(channel1RadioButton);
			channel1RadioButton.setSelected(true);
			JRadioButton channel2RadioButton = new JRadioButton("Channel 2");
			scale(channel2RadioButton);
			channel2RadioButton.setSelected(false);
			JRadioButton channel3RadioButton = new JRadioButton("Channel 3");
			scale(channel3RadioButton);
			channel3RadioButton.setSelected(false);
			JRadioButton channel4RadioButton = new JRadioButton("Channel 4");
			scale(channel4RadioButton);
			channel4RadioButton.setSelected(false);
			JRadioButton channel5RadioButton = new JRadioButton("Channel 5");
			scale(channel5RadioButton);
			channel5RadioButton.setSelected(false);
			JRadioButton channel6RadioButton = new JRadioButton("Channel 6");
			scale(channel6RadioButton);
			channel6RadioButton.setSelected(false);
			JRadioButton channel7RadioButton = new JRadioButton("Channel 7");
			scale(channel7RadioButton);
			channel7RadioButton.setSelected(false);

			JPanel currentchannelPanel = new JPanel();
			currentchannelPanel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout currentchannelPanelLayout = new GridBagLayout();
			GridBagConstraints currentchannelPanelConstraints = new GridBagConstraints();
			currentchannelPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			currentchannelPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			currentchannelPanelConstraints.gridwidth = 1;
			currentchannelPanelConstraints.gridheight = 1;
			currentchannelPanelConstraints.gridx = 0;
			currentchannelPanelConstraints.gridy = 0;
			currentchannelPanel.setLayout(currentchannelPanelLayout);
			currentchannelPanel.add(channel1RadioButton,currentchannelPanelConstraints);
			currentchannelPanelConstraints.gridy++;
			if(numOfChannels>1) {
				currentchannelPanel.add(channel2RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>2) {
				currentchannelPanel.add(channel3RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>3) {
				currentchannelPanel.add(channel4RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>4) {
				currentchannelPanel.add(channel5RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>5) {
				currentchannelPanel.add(channel6RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			if(numOfChannels>6) {
				currentchannelPanel.add(channel7RadioButton,currentchannelPanelConstraints);
				currentchannelPanelConstraints.gridy++;
			}
			ButtonGroup bg3=new ButtonGroup();
			switch (numOfChannels) {
			case 1:
				bg3.add(channel1RadioButton);				
				break;
			case 2:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);
				break;
			case 3:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);
				break;
			case 4:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);
				break;
			case 5:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);bg3.add(channel5RadioButton);
				break;
			case 6:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);bg3.add(channel5RadioButton);bg3.add(channel6RadioButton);
				break;
			case 7:
				bg3.add(channel1RadioButton);bg3.add(channel2RadioButton);bg3.add(channel3RadioButton);bg3.add(channel4RadioButton);bg3.add(channel5RadioButton);bg3.add(channel6RadioButton);bg3.add(channel7RadioButton);
				break;
			default:
				break;
			}


			GenericDialogPlus gd3 = new GenericDialogPlus("Channel associated with the marker");
			gd3.addMessage("Which channel is associated with this marker?");
			gd3.addComponent(currentchannelPanel);
			gd3.showDialog();

			if (gd3.wasCanceled())
				return false;

			chosenChannelForObjectAssociatedMarker = 1;
			if(channel2RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker= 2;}
			else if(channel3RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 3;}
			else if(channel4RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 4;}
			else if(channel5RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 5;}
			else if(channel6RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 6;}
			else if(channel7RadioButton.isSelected()) {chosenChannelForObjectAssociatedMarker = 7;}
			channelsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1] = chosenChannelForObjectAssociatedMarker;

			currentMode = 1;
			currentObjectAssociatedMarker = numOfObjectAssociatedMarkers-1;
			currentPattern = 0;

			repaintWindow();
			updateAnnotateObjectAssociatedMarker(numOfObjectAssociatedMarkers-1,false);
		}

		return true;	
	}
	/** remove incompatible markers associated nuclei */ 
	private void removeIncompatibility(int markerToRemove, int markerToRemain) {
		for(int i=0;i<positiveNucleiForEachMarker[markerToRemove][0].size();i++) {
			for(int j=0;j<positiveNucleiForEachMarker[markerToRemain][0].size();j++) {
				if(positiveNucleiForEachMarker[markerToRemove][0].get(i).equals(positiveNucleiForEachMarker[markerToRemain][0].get(j))) {
					positiveNucleiForEachMarker[markerToRemove][0].remove(i);
					i--;
					j = positiveNucleiForEachMarker[markerToRemain][0].size();
				}
			}
		}
	}
	/** open a new image and segmentation image to label other nuclei */
	void loadNucleiAndSegmentation(){
		imageFolder = "Null";
		imageFile = "Null";
		segmentationFolder = "Null";
		segmentationFile = "Null";
		
		/** JButton for batch processing */
		JButton imageFolderButton = new JButton("Image folder");
		scale(imageFolderButton);
		JButton segmentationFolderButton = new JButton("Object segmentation folder");
		scale(segmentationFolderButton);
		
		JTextArea imageFolderQuestion = new JTextArea("Choose the new input image");
		scale(imageFolderQuestion);
		imageFolderQuestion.setEditable(false);
		JTextArea segmentationFolderQuestion = new JTextArea("Choose the new segmented image");
		scale(segmentationFolderQuestion);
		segmentationFolderQuestion.setEditable(false);
		
		JPanel batchPanel = new JPanel();
		batchPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout batchPanelLayout = new GridBagLayout();
		GridBagConstraints batchPanelConstraints = new GridBagConstraints();
		batchPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		batchPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		batchPanelConstraints.gridwidth = 1;
		batchPanelConstraints.gridheight = 1;
		batchPanelConstraints.gridx = 0;
		batchPanelConstraints.gridy = 0;
		batchPanel.setLayout(batchPanelLayout);

		batchPanel.add(imageFolderQuestion,batchPanelConstraints);
		batchPanelConstraints.gridx++;
		batchPanel.add(imageFolderButton,batchPanelConstraints);
		batchPanelConstraints.gridy++;
		batchPanelConstraints.gridx=0;
		batchPanel.add(segmentationFolderQuestion,batchPanelConstraints);
		batchPanelConstraints.gridx++;
		batchPanel.add(segmentationFolderButton,batchPanelConstraints);
		batchPanelConstraints.gridy++;
		batchPanelConstraints.gridx=0;
		
		GenericDialogPlus gd = new GenericDialogPlus("Open new image");
		gd.addComponent(batchPanel);

		imageFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				OpenDialog imageChooser = new OpenDialog("Input image");
				imageFolder = imageChooser.getDirectory();
				imageFile = imageChooser.getFileName();
			}
		});
		segmentationFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				OpenDialog segmentationChooser = new OpenDialog("Segmentated image");
				segmentationFolder = segmentationChooser.getDirectory();
				segmentationFile = segmentationChooser.getFileName();
			}
		});

		gd.showDialog();
		if (gd.wasCanceled()) {
			for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
			for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
			return;
		}

		if (gd.wasOKed()) {
			for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
			for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
			if(imageFolder=="Null") {
				IJ.showMessage("You need to define a new input image");
				return;
			}
			if(segmentationFolder=="Null") {
				IJ.showMessage("You need to define a new segmented image");
				return;
			}
			// store features for training if any
			storeFeaturesForTraining();
			
			//	storing all information needed to identify objects associated markers with thresholding
			byte[] markerCellcompartmentMem = new byte[]{0,0,0,0,0,0,0}; 
			byte[] channelsForObjectAssociatedMarkersMem = new byte[]{-1,-1,-1,-1,-1,-1,-1};
			int[][] thresholdsForObjectAssociatedMarkersMem = new int[][]{{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1}};
			byte[] methodToIdentifyObjectAssociatedMarkersMem = new byte[]{0,0,0,0,0,0,0};
			List<double[]> [] featuresForEachMarkerMem = new ArrayList[MAX_NUM_MARKERS];
			
			for(int p=0;p<numOfObjectAssociatedMarkers;p++) {
				markerCellcompartmentMem[p] = markerCellcompartment[p];
				channelsForObjectAssociatedMarkersMem[p] = channelsForObjectAssociatedMarkers[p];
				thresholdsForObjectAssociatedMarkersMem[p][0] = thresholdsForObjectAssociatedMarkers[p][0];
				thresholdsForObjectAssociatedMarkersMem[p][1] = thresholdsForObjectAssociatedMarkers[p][1];
				methodToIdentifyObjectAssociatedMarkersMem[p] = methodToIdentifyObjectAssociatedMarkers[p];
				featuresForEachMarkerMem[p] = featuresForEachMarker[p];
			}
			
			win.close();

			Opener opener = new Opener();
			displayImage = opener.openImage(imageFolder+imageFile);

			int[] dims = displayImage.getDimensions();
			if((dims[2]==1)&&(dims[3]==1)&&(dims[4]==1)) {
				ImageConverter ic = new ImageConverter(displayImage);
				ic.convertToRGB();
			}

			if(displayImage.getType()==4) {
				displayImage = CompositeConverter.makeComposite(displayImage);
				dims = displayImage.getDimensions();
			}

			if(dims[2]==1) {
				if((dims[3]>1)&&(dims[4]==1)) {
					displayImage = HyperStackConverter.toHyperStack(displayImage, dims[3], 1, 1);
				}
				if((dims[4]>1)&&(dims[3]==1)) {
					displayImage = HyperStackConverter.toHyperStack(displayImage, dims[4], 1, 1);
				}
				dims = displayImage.getDimensions();
			}

			numOfChannels = (byte)dims[2];

			if(numOfChannels>7) {
				IJ.showMessage("Too many channels", "Images cannot exceed 7 channels");
				return;
			}
			if((dims[3]>1)||(dims[4]>1)) {
				IJ.showMessage("2D image", "Only 2D multi-channel images are accepted");
				return;
			}

			// reinitialization of objects and areas
			roiFlag = new short [displayImage.getWidth()][displayImage.getHeight()][3];
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					roiFlag[x][y][0] = -1;
					roiFlag[x][y][1] = -1;
					roiFlag[x][y][2] = -1;
				}
			}
			for(int c=0;c<numOfAreas;c++) {
				areasInEachClass[c] = null;
			}
			areasInEachClass[0] = new ArrayList<Point[]>();
			numOfAreas = 1;
			// update flags for cell compartment computation
			nuclearComponentFlag = false;
			innerNuclearComponentFlag = false;
			membranarComponentFlag = false;
			cytoplasmicComponentFlag = false;
			rt_nuclearML_flag = false;
			
			ImagePlus segmentedImage = opener.openImage(segmentationFolder+segmentationFile);
			int actualNumOfObjectAssociatedMarkers = numOfObjectAssociatedMarkers;
			currentObjectAssociatedMarker = -1;
			initializeMarkerButtons();
			loadNucleiSegmentations(segmentedImage);

			for(int p=0;p<actualNumOfObjectAssociatedMarkers;p++) {
				addNewMarker();
				
				markerCellcompartment[p] = markerCellcompartmentMem[p];
				channelsForObjectAssociatedMarkers[p] = channelsForObjectAssociatedMarkersMem[p];
				thresholdsForObjectAssociatedMarkers[p][0] = thresholdsForObjectAssociatedMarkersMem[p][0];
				thresholdsForObjectAssociatedMarkers[p][1] = thresholdsForObjectAssociatedMarkersMem[p][1];
				featuresForEachMarker[p] = featuresForEachMarkerMem[p];
				methodToIdentifyObjectAssociatedMarkers[p] = methodToIdentifyObjectAssociatedMarkersMem[p];
				
				updateAnnotateObjectAssociatedMarker(numOfObjectAssociatedMarkers-1,false);
				if(methodToIdentifyObjectAssociatedMarkers[p]==1){
					if(channelsForObjectAssociatedMarkers[p]>(-1)) {
						List<Polygon> [] cellComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];
						for(int i=0;i<numOfClasses;i++) {
							cellComponentInEachClass[i] = new ArrayList<Polygon>();
						}
						for(int i=0;i<numOfClasses;i++) {
							for(int j=0;j<objectsInEachClass[i].size();j++) {
								Polygon fp = new Polygon();
								cellComponentInEachClass[i].add(fp);
							}
						}

						if(markerCellcompartment[p]==0) {
							if(!nuclearComponentFlag){
								computeNuclearComponent();
								nuclearComponentFlag = true;
							}
							for(int i=0;i<numOfClasses;i++) {
								for(int y=0;y<displayImage.getHeight();y++) {
									for(int x=0;x<displayImage.getWidth();x++) {
										if(nuclearComponent[i][x][y]>0) {
											cellComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
										}
									}
								}
							}
						}
						else if(markerCellcompartment[p]==1) {
							if(!nuclearComponentFlag){
								computeNuclearComponent();
								nuclearComponentFlag = true;
							}
							if(!innerNuclearComponentFlag){
								computeInnerNuclearComponent();
								innerNuclearComponentFlag = true;
							}
							if(!membranarComponentFlag){
								computeMembranarComponent();
								membranarComponentFlag = true;
							}
							for(int i=0;i<numOfClasses;i++) {
								for(int y=0;y<displayImage.getHeight();y++) {
									for(int x=0;x<displayImage.getWidth();x++) {
										if(membranarComponent[i][x][y]>0) {
											cellComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
										}
									}
								}
							}
						}
						else if(markerCellcompartment[p]==2) {
							if(!nuclearComponentFlag){
								computeNuclearComponent();
								nuclearComponentFlag = true;
							}
							if(!innerNuclearComponentFlag){
								computeInnerNuclearComponent();
								innerNuclearComponentFlag = true;
							}
							if(!cytoplasmicComponentFlag){
								computeCytoplasmicComponent();
								cytoplasmicComponentFlag = true;
							}
							for(int i=0;i<numOfClasses;i++) {
								for(int y=0;y<displayImage.getHeight();y++) {
									for(int x=0;x<displayImage.getWidth();x++) {
										if(cytoplasmicComponent[i][x][y]>0) {
											cellComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
										}
									}
								}
							}
						}
						chosenChannelForObjectAssociatedMarker = channelsForObjectAssociatedMarkers[p];
						areaThresholdingScrollBar.setValue(thresholdsForObjectAssociatedMarkers[p][0]);
						intensityThresholdingForObjectAssociatedMarkerScrollBar.setValue(thresholdsForObjectAssociatedMarkers[p][1]);
						computeIntensityThresholdForEachObject(cellComponentInEachClass);
						roiActivationAndDeactivationBasedOnThresholding();
					}
					removeMarkersFromOverlay();
					updateModeRadioButtons(1);
				}
				else if(methodToIdentifyObjectAssociatedMarkers[p]==2){
					train(p);
					removeMarkersFromOverlay();
					updateModeRadioButtons(1);
				}
			}
		}
		currentObjectAssociatedMarker = -1;
		removeMarkersFromOverlay();
		repaintWindow();
	}
	/** batch process markers */ 
	/**
	 * 
	 */
	private void batchProcessing(int mode)
	{
		boolean objectBatchProcess = false, markerProcessingBatchProcess = false;
		if(mode==1){
			JLabel label1 = new JLabel("Do you want to batch process marker associated objects?");
			scale(label1);
			switch ( JOptionPane.showConfirmDialog( null, label1, "Objects", JOptionPane.YES_NO_OPTION ) )
			{
			case JOptionPane.YES_OPTION:
				objectBatchProcess = true;
				break;
			case JOptionPane.NO_OPTION:
				objectBatchProcess = false;
				break;
			}
			if(objectBatchProcess){
				boolean goodToGo = false;
				for(int i=0;i<MAX_NUM_MARKERS;i++){
					if(methodToIdentifyObjectAssociatedMarkers[i]>0){goodToGo = true;}
				}
				if(goodToGo){
					/** buttons for marker characterization method */
					JRadioButton thresholdRadioButton = new JRadioButton("With the previously defined thresholding and/or machine learning methods");
					scale(thresholdRadioButton);
					thresholdRadioButton.setSelected(true);
					JRadioButton fileRadioButton = new JRadioButton("From images");
					scale(fileRadioButton);
					fileRadioButton.setSelected(false);
					if(goodToGo){
						ButtonGroup bg1=new ButtonGroup();    
						bg1.add(thresholdRadioButton);
						bg1.add(fileRadioButton);

						JPanel markerMethodPanel = new JPanel();
						markerMethodPanel.setBorder(BorderFactory.createTitledBorder(""));
						GridBagLayout markerMethodPanelLayout = new GridBagLayout();
						GridBagConstraints markerMethodPanelConstraints = new GridBagConstraints();
						markerMethodPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
						markerMethodPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
						markerMethodPanelConstraints.gridwidth = 1;
						markerMethodPanelConstraints.gridheight = 1;
						markerMethodPanelConstraints.gridx = 0;
						markerMethodPanelConstraints.gridy = 0;
						markerMethodPanel.setLayout(markerMethodPanelLayout);
						markerMethodPanel.add(fileRadioButton,markerMethodPanelConstraints);
						markerMethodPanelConstraints.gridy++;
						markerMethodPanel.add(thresholdRadioButton,markerMethodPanelConstraints);

						GenericDialogPlus gd1 = new GenericDialogPlus("Marker associated objects");
						gd1.addMessage("How do you want to define marker associated objects?");
						gd1.addComponent(markerMethodPanel);
						gd1.showDialog();

						if (gd1.wasCanceled()){
							objectBatchProcess = false;
							markerProcessingBatchProcess = false;
						}

					}
					if(thresholdRadioButton.isSelected()) {
						markerProcessingBatchProcess = true;
					}
				}
			}
		}
		boolean areaBatchProcess = false;
		JLabel label2 = new JLabel("Do you want to add images to define areas?");
		scale(label2);
		switch ( JOptionPane.showConfirmDialog( null, label2, "Region", JOptionPane.YES_NO_OPTION ) )
		{
		case JOptionPane.YES_OPTION:
			areaBatchProcess = true;
			break;
		case JOptionPane.NO_OPTION:
			areaBatchProcess = false;
			break;
		}
		boolean outputImageBatchProcess = false;
		JLabel label3 = new JLabel("Do you want to batch process result images for visual inspection?");
		scale(label3);
		switch ( JOptionPane.showConfirmDialog( null, label3, "Result image", JOptionPane.YES_NO_OPTION ) )
		{
		case JOptionPane.YES_OPTION:
			outputImageBatchProcess = true;
			break;
		case JOptionPane.NO_OPTION:
			outputImageBatchProcess = false;
			break;
		}

		imageFolder = "Null";
		segmentationFolder = "Null";
		objectAssociatedMarkerFolder = "Null";
		areaFolder = "Null";
		measurementsFolder = "Null";
		outputImageFolder = "Null";

		/** JButton for batch processing */
		JButton imageFolderButton = new JButton("Image folder");
		scale(imageFolderButton);
		JButton segmentationFolderButton = new JButton("Object segmentation folder");
		scale(segmentationFolderButton);
		JButton objectAssociatedMarkerFolderButton = new JButton("Marker associated object folder");
		scale(objectAssociatedMarkerFolderButton);
		JButton areaAssociatedMarkerFolderButton = new JButton("Region segmentation folder");
		scale(areaAssociatedMarkerFolderButton);
		JButton measurementsFolderButton = new JButton("Measurements folder");
		scale(measurementsFolderButton);
		JButton outputImageFolderButton = new JButton("Result image folder");
		scale(outputImageFolderButton);

		JTextArea imageFolderQuestion = new JTextArea("Where is the folder with the input images?");
		scale(imageFolderQuestion);
		imageFolderQuestion.setEditable(false);
		JTextArea areaAssociatedMarkerFolderQuestion = new JTextArea("Where is the folder with the segmented area images?");
		scale(areaAssociatedMarkerFolderQuestion);
		areaAssociatedMarkerFolderQuestion.setEditable(false);
		JTextArea segmentationFolderQuestion = new JTextArea("Where is the folder with the segmented object images?");
		scale(segmentationFolderQuestion);
		segmentationFolderQuestion.setEditable(false);
		JTextArea objectAssociatedMarkerFolderQuestion = new JTextArea("Where is the destination folder for the marker associated object images?");
		scale(objectAssociatedMarkerFolderQuestion);
		objectAssociatedMarkerFolderQuestion.setEditable(false);
		JTextArea measurementsFolderQuestion = new JTextArea("Where is the destination folder for the measurements?");
		scale(measurementsFolderQuestion);
		measurementsFolderQuestion.setEditable(false);
		JTextArea outputImageFolderQuestion = new JTextArea("Where is the destination folder for the result images?");
		scale(outputImageFolderQuestion);
		outputImageFolderQuestion.setEditable(false);

		JPanel batchPanel = new JPanel();
		batchPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout batchPanelLayout = new GridBagLayout();
		GridBagConstraints batchPanelConstraints = new GridBagConstraints();
		batchPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		batchPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		batchPanelConstraints.gridwidth = 1;
		batchPanelConstraints.gridheight = 1;
		batchPanelConstraints.gridx = 0;
		batchPanelConstraints.gridy = 0;
		batchPanel.setLayout(batchPanelLayout);

		batchPanel.add(imageFolderQuestion,batchPanelConstraints);
		batchPanelConstraints.gridx++;
		batchPanel.add(imageFolderButton,batchPanelConstraints);
		batchPanelConstraints.gridy++;
		batchPanelConstraints.gridx=0;
		batchPanel.add(segmentationFolderQuestion,batchPanelConstraints);
		batchPanelConstraints.gridx++;
		batchPanel.add(segmentationFolderButton,batchPanelConstraints);
		batchPanelConstraints.gridy++;
		batchPanelConstraints.gridx=0;
		if(areaBatchProcess){
			batchPanel.add(areaAssociatedMarkerFolderQuestion,batchPanelConstraints);
			batchPanelConstraints.gridx++;
			batchPanel.add(areaAssociatedMarkerFolderButton,batchPanelConstraints);
			batchPanelConstraints.gridy++;
			batchPanelConstraints.gridx=0;
		}
		if(objectBatchProcess){
			batchPanel.add(objectAssociatedMarkerFolderQuestion,batchPanelConstraints);
			batchPanelConstraints.gridx++;
			batchPanel.add(objectAssociatedMarkerFolderButton,batchPanelConstraints);
			batchPanelConstraints.gridy++;
			batchPanelConstraints.gridx=0;
		}
		batchPanel.add(measurementsFolderQuestion,batchPanelConstraints);
		batchPanelConstraints.gridx++;
		batchPanel.add(measurementsFolderButton,batchPanelConstraints);
		batchPanelConstraints.gridy++;
		batchPanelConstraints.gridx=0;
		if(outputImageBatchProcess){
			batchPanel.add(outputImageFolderQuestion,batchPanelConstraints);
			batchPanelConstraints.gridx++;
			batchPanel.add(outputImageFolderButton,batchPanelConstraints);
			batchPanelConstraints.gridy++;
		}

		GenericDialogPlus gd = new GenericDialogPlus("Batch processing");
		gd.addComponent(batchPanel);

		imageFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser imageChooser = new DirectoryChooser("Input image folder");
				imageFolder = imageChooser.getDirectory();
			}
		});
		segmentationFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser segmentationChooser = new DirectoryChooser("Object segmentation folder");
				segmentationFolder = segmentationChooser.getDirectory();
			}
		});
		areaAssociatedMarkerFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser areaAssociatedMarkerChooser = new DirectoryChooser("Region segmentation folder");
				areaFolder = areaAssociatedMarkerChooser.getDirectory();
			}
		});
		objectAssociatedMarkerFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser objectAssociatedMarkerChooser = new DirectoryChooser("Marker associated object folder");
				objectAssociatedMarkerFolder = objectAssociatedMarkerChooser.getDirectory();
			}
		});
		measurementsFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser measurementsChooser = new DirectoryChooser("Measurements folder");
				measurementsFolder = measurementsChooser.getDirectory();
			}
		});
		outputImageFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser outputImageChooser = new DirectoryChooser("Result image folder");
				outputImageFolder = outputImageChooser.getDirectory();
			}
		});

		gd.showDialog();

		if (gd.wasCanceled()) {
			for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
			for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
			for( ActionListener al : objectAssociatedMarkerFolderButton.getActionListeners() ) {objectAssociatedMarkerFolderButton.removeActionListener( al );}
			for( ActionListener al : areaAssociatedMarkerFolderButton.getActionListeners() ) {areaAssociatedMarkerFolderButton.removeActionListener( al );}
			for( ActionListener al : measurementsFolderButton.getActionListeners() ) {measurementsFolderButton.removeActionListener( al );}
			for( ActionListener al : outputImageFolderButton.getActionListeners() ) {outputImageFolderButton.removeActionListener( al );}
			return;
		}

		if (gd.wasOKed()) {
			for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
			for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
			for( ActionListener al : objectAssociatedMarkerFolderButton.getActionListeners() ) {objectAssociatedMarkerFolderButton.removeActionListener( al );}
			for( ActionListener al : areaAssociatedMarkerFolderButton.getActionListeners() ) {areaAssociatedMarkerFolderButton.removeActionListener( al );}
			for( ActionListener al : measurementsFolderButton.getActionListeners() ) {measurementsFolderButton.removeActionListener( al );}
			for( ActionListener al : outputImageFolderButton.getActionListeners() ) {outputImageFolderButton.removeActionListener( al );}
			if(imageFolder=="Null") {
				IJ.showMessage("You need to define a folder with the input images to process.");
				return;
			}
			if(segmentationFolder=="Null") {
				IJ.showMessage("You need to define a folder with the segmented object images to process.");
				return;
			}
			if(objectBatchProcess) {
				if(objectAssociatedMarkerFolder=="Null") {
					IJ.showMessage("You need to define a folder with the marker associated object images associated with the input images to process.");
					return;
				}
			}
			if(areaBatchProcess) {
				if(areaFolder=="Null") {
					IJ.showMessage("You need to define a folder with the segmented area images to process.");
					return;
				}
			}
			if(measurementsFolder=="Null") {
				IJ.showMessage("You need to define a destination folder for the measurements.");
				return;
			}
			if(outputImageBatchProcess) {
				if(outputImageFolder=="Null") {
					IJ.showMessage("You need to define a folder with the result images associated with the input images to process.");
					return;
				}
			}
			File imageFile = new File(imageFolder), segmentationFile = new File(segmentationFolder), objectAssociatedMarkerFile = new File(objectAssociatedMarkerFolder), areaAssociatedMarkerFile = new File(areaFolder), measurementsFile = new File(measurementsFolder), outputImageFile = new File(outputImageFolder);
			for (File imageFileEntry : imageFile.listFiles()) {
				if (!imageFileEntry.isDirectory()) {
					String[] currentImageFile = imageFileEntry.getName().split("\\.");
					if (currentImageFile.length > 1) {
						if ((currentImageFile[1].equals("tiff")) || (currentImageFile[1].equals("tif")) || (currentImageFile[1].equals("png"))){
							boolean ok=false;
							for (File segmentationFileEntry : segmentationFile.listFiles()) {
								String[] currentSegmentationFile = segmentationFileEntry.getName().split("\\.");
								if(currentSegmentationFile[0].equals(currentImageFile[0])) {ok=true;}
							}
							if(!ok) {
								IJ.showMessage("For each input image in the input image folder, there must be a segmented object image with the same name in the segmentation folder.");
								return;
							}
							if(objectBatchProcess&&!markerProcessingBatchProcess) {
								ok = false;
								for (File markerFileEntry : objectAssociatedMarkerFile.listFiles()) {
									String[] markerSegmentationFile = markerFileEntry.getName().split("\\.");
									if(markerSegmentationFile[0].equals(currentImageFile[0])) {ok=true;}
								}
								if(!ok) {
									IJ.showMessage("For each input image in the input image folder, there must be a marker associated object image with the same name in the object folder.");
									return;
								}
							}
							if(areaBatchProcess) {
								ok = false;
								for (File markerFileEntry : areaAssociatedMarkerFile.listFiles()) {
									String[] markerSegmentationFile = markerFileEntry.getName().split("\\.");
									if(markerSegmentationFile[0].equals(currentImageFile[0])) {ok=true;}
								}
								if(!ok) {
									IJ.showMessage("For each input image in the input image folder, there must be a segmented area image with the same name in the area folder.");
									return;
								}
							}
						}
					}
				}
			}


			JTextArea marker1Sentence = new JTextArea("Marker 1 does not coincide with:");
			scale(marker1Sentence);
			marker1Sentence.setEditable(false);
			JRadioButton marker1RadioButton_1 = new JRadioButton("Marker 1");
			scale(marker1RadioButton_1);
			marker1RadioButton_1.setEnabled(false);
			JRadioButton marker2RadioButton_1 = new JRadioButton("Marker 2");
			scale(marker2RadioButton_1);
			marker2RadioButton_1.setSelected(false);
			JRadioButton marker3RadioButton_1 = new JRadioButton("Marker 3");
			scale(marker3RadioButton_1);
			marker3RadioButton_1.setSelected(false);
			JRadioButton marker4RadioButton_1 = new JRadioButton("Marker 4");
			scale(marker4RadioButton_1);
			marker4RadioButton_1.setSelected(false);
			JRadioButton marker5RadioButton_1 = new JRadioButton("Marker 5");
			scale(marker5RadioButton_1);
			marker5RadioButton_1.setSelected(false);
			JRadioButton marker6RadioButton_1 = new JRadioButton("Marker 6");
			scale(marker6RadioButton_1);
			marker6RadioButton_1.setSelected(false);
			JRadioButton marker7RadioButton_1 = new JRadioButton("Marker 7");
			scale(marker7RadioButton_1);
			marker7RadioButton_1.setSelected(false);

			JTextArea marker2Sentence = new JTextArea("Marker 2 does not coincide with:");
			scale(marker2Sentence);
			marker2Sentence.setEditable(false);
			JRadioButton marker1RadioButton_2 = new JRadioButton("Marker 1");
			scale(marker1RadioButton_2);
			marker1RadioButton_2.setSelected(false);
			JRadioButton marker2RadioButton_2 = new JRadioButton("Marker 2");
			scale(marker2RadioButton_2);
			marker2RadioButton_2.setEnabled(false);
			JRadioButton marker3RadioButton_2 = new JRadioButton("Marker 3");
			scale(marker3RadioButton_2);
			marker3RadioButton_2.setSelected(false);
			JRadioButton marker4RadioButton_2 = new JRadioButton("Marker 4");
			scale(marker4RadioButton_2);
			marker4RadioButton_2.setSelected(false);
			JRadioButton marker5RadioButton_2 = new JRadioButton("Marker 5");
			scale(marker5RadioButton_2);
			marker5RadioButton_2.setSelected(false);
			JRadioButton marker6RadioButton_2 = new JRadioButton("Marker 6");
			scale(marker6RadioButton_2);
			marker6RadioButton_2.setSelected(false);
			JRadioButton marker7RadioButton_2 = new JRadioButton("Marker 7");
			scale(marker7RadioButton_2);
			marker7RadioButton_2.setSelected(false);

			JTextArea marker3Sentence = new JTextArea("Marker 3 does not coincide with:");
			scale(marker3Sentence);
			marker3Sentence.setEditable(false);
			JRadioButton marker1RadioButton_3 = new JRadioButton("Marker 1");
			scale(marker1RadioButton_3);
			marker1RadioButton_3.setSelected(false);
			JRadioButton marker2RadioButton_3 = new JRadioButton("Marker 2");
			scale(marker2RadioButton_3);
			marker2RadioButton_3.setSelected(false);
			JRadioButton marker3RadioButton_3 = new JRadioButton("Marker 3");
			scale(marker3RadioButton_3);
			marker3RadioButton_3.setEnabled(false);
			JRadioButton marker4RadioButton_3 = new JRadioButton("Marker 4");
			scale(marker4RadioButton_3);
			marker4RadioButton_3.setSelected(false);
			JRadioButton marker5RadioButton_3 = new JRadioButton("Marker 5");
			scale(marker5RadioButton_3);
			marker5RadioButton_3.setSelected(false);
			JRadioButton marker6RadioButton_3 = new JRadioButton("Marker 6");
			scale(marker6RadioButton_3);
			marker6RadioButton_3.setSelected(false);
			JRadioButton marker7RadioButton_3 = new JRadioButton("Marker 7");
			scale(marker7RadioButton_3);
			marker7RadioButton_3.setSelected(false);

			JTextArea marker4Sentence = new JTextArea("Marker 4 does not coincide with:");
			scale(marker4Sentence);
			marker4Sentence.setEditable(false);
			JRadioButton marker1RadioButton_4 = new JRadioButton("Marker 1");
			scale(marker1RadioButton_4);
			marker1RadioButton_4.setSelected(false);
			JRadioButton marker2RadioButton_4 = new JRadioButton("Marker 2");
			scale(marker1RadioButton_4);
			marker2RadioButton_4.setSelected(false);
			JRadioButton marker3RadioButton_4 = new JRadioButton("Marker 3");
			scale(marker3RadioButton_4);
			marker3RadioButton_4.setSelected(false);
			JRadioButton marker4RadioButton_4 = new JRadioButton("Marker 4");
			scale(marker4RadioButton_4);
			marker4RadioButton_4.setEnabled(false);
			JRadioButton marker5RadioButton_4 = new JRadioButton("Marker 5");
			scale(marker5RadioButton_4);
			marker5RadioButton_4.setSelected(false);
			JRadioButton marker6RadioButton_4 = new JRadioButton("Marker 6");
			scale(marker6RadioButton_4);
			marker6RadioButton_4.setSelected(false);
			JRadioButton marker7RadioButton_4 = new JRadioButton("Marker 7");
			scale(marker7RadioButton_4);
			marker7RadioButton_4.setSelected(false);

			JTextArea marker5Sentence = new JTextArea("Marker 5 does not coincide with:");
			scale(marker5Sentence);
			marker5Sentence.setEditable(false);
			JRadioButton marker1RadioButton_5 = new JRadioButton("Marker 1");
			scale(marker1RadioButton_5);
			marker1RadioButton_5.setSelected(false);
			JRadioButton marker2RadioButton_5 = new JRadioButton("Marker 2");
			scale(marker2RadioButton_5);
			marker2RadioButton_5.setSelected(false);
			JRadioButton marker3RadioButton_5 = new JRadioButton("Marker 3");
			scale(marker3RadioButton_5);
			marker3RadioButton_5.setSelected(false);
			JRadioButton marker4RadioButton_5 = new JRadioButton("Marker 4");
			scale(marker4RadioButton_5);
			marker4RadioButton_5.setSelected(false);
			JRadioButton marker5RadioButton_5 = new JRadioButton("Marker 5");
			scale(marker5RadioButton_5);
			marker5RadioButton_5.setEnabled(false);
			JRadioButton marker6RadioButton_5 = new JRadioButton("Marker 6");
			scale(marker6RadioButton_5);
			marker6RadioButton_5.setSelected(false);
			JRadioButton marker7RadioButton_5 = new JRadioButton("Marker 7");
			scale(marker7RadioButton_5);
			marker7RadioButton_5.setSelected(false);

			JTextArea marker6Sentence = new JTextArea("Marker 6 does not coincide with:");
			scale(marker6Sentence);
			marker6Sentence.setEditable(false);
			JRadioButton marker1RadioButton_6 = new JRadioButton("Marker 1");
			scale(marker1RadioButton_6);
			marker1RadioButton_6.setSelected(false);
			JRadioButton marker2RadioButton_6 = new JRadioButton("Marker 2");
			scale(marker2RadioButton_6);
			marker2RadioButton_6.setSelected(false);
			JRadioButton marker3RadioButton_6 = new JRadioButton("Marker 3");
			scale(marker3RadioButton_6);
			marker3RadioButton_6.setSelected(false);
			JRadioButton marker4RadioButton_6 = new JRadioButton("Marker 4");
			scale(marker4RadioButton_6);
			marker4RadioButton_6.setSelected(false);
			JRadioButton marker5RadioButton_6 = new JRadioButton("Marker 5");
			scale(marker5RadioButton_6);
			marker5RadioButton_6.setSelected(false);
			JRadioButton marker6RadioButton_6 = new JRadioButton("Marker 6");
			scale(marker6RadioButton_6);
			marker6RadioButton_6.setEnabled(false);
			JRadioButton marker7RadioButton_6 = new JRadioButton("Marker 7");
			scale(marker7RadioButton_6);
			marker7RadioButton_6.setSelected(false);

			JTextArea marker7Sentence = new JTextArea("Marker 7 does not coincide with:");
			scale(marker7Sentence);
			marker7Sentence.setEditable(false);
			JRadioButton marker1RadioButton_7 = new JRadioButton("Marker 1");
			scale(marker1RadioButton_7);
			marker1RadioButton_7.setSelected(false);
			JRadioButton marker2RadioButton_7 = new JRadioButton("Marker 2");
			scale(marker2RadioButton_7);
			marker2RadioButton_7.setSelected(false);
			JRadioButton marker3RadioButton_7 = new JRadioButton("Marker 3");
			scale(marker3RadioButton_7);
			marker3RadioButton_7.setSelected(false);
			JRadioButton marker4RadioButton_7 = new JRadioButton("Marker 4");
			scale(marker4RadioButton_7);
			marker4RadioButton_7.setSelected(false);
			JRadioButton marker5RadioButton_7 = new JRadioButton("Marker 5");
			scale(marker5RadioButton_7);
			marker5RadioButton_7.setSelected(false);
			JRadioButton marker6RadioButton_7 = new JRadioButton("Marker 6");
			scale(marker6RadioButton_7);
			marker6RadioButton_7.setSelected(false);
			JRadioButton marker7RadioButton_7 = new JRadioButton("Marker 7");
			scale(marker7RadioButton_7);
			marker7RadioButton_7.setEnabled(false);

			if(objectBatchProcess){
				if(numOfObjectAssociatedMarkers>1) {
					JPanel nonOverlappingMarkersPanel1_1 = new JPanel(), nonOverlappingMarkersPanel1_2 = new JPanel();
					nonOverlappingMarkersPanel1_1.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout1_1 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints1_1 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints1_1.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints1_1.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints1_1.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints1_1.gridheight = 1;
					nonOverlappingMarkersPanelConstraints1_1.gridx = 0;
					nonOverlappingMarkersPanelConstraints1_1.gridy = 0;
					nonOverlappingMarkersPanel1_1.setLayout(nonOverlappingMarkersPanelLayout1_1);
					nonOverlappingMarkersPanel1_2.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout1_2 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints1_2 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints1_2.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints1_2.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints1_2.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints1_2.gridheight = 1;
					nonOverlappingMarkersPanelConstraints1_2.gridx = 0;
					nonOverlappingMarkersPanelConstraints1_2.gridy = 0;
					nonOverlappingMarkersPanel1_2.setLayout(nonOverlappingMarkersPanelLayout1_2);
					JPanel nonOverlappingMarkersPanel2_1 = new JPanel(), nonOverlappingMarkersPanel2_2 = new JPanel();
					nonOverlappingMarkersPanel2_1.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout2_1 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints2_1 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints2_1.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints2_1.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints2_1.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints2_1.gridheight = 1;
					nonOverlappingMarkersPanelConstraints2_1.gridx = 0;
					nonOverlappingMarkersPanelConstraints2_1.gridy = 0;
					nonOverlappingMarkersPanel2_1.setLayout(nonOverlappingMarkersPanelLayout2_1);
					nonOverlappingMarkersPanel2_2.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout2_2 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints2_2 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints2_2.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints2_2.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints2_2.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints2_2.gridheight = 1;
					nonOverlappingMarkersPanelConstraints2_2.gridx = 0;
					nonOverlappingMarkersPanelConstraints2_2.gridy = 0;
					nonOverlappingMarkersPanel2_2.setLayout(nonOverlappingMarkersPanelLayout2_2);
					JPanel nonOverlappingMarkersPanel3_1 = new JPanel(), nonOverlappingMarkersPanel3_2 = new JPanel();
					nonOverlappingMarkersPanel3_1.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout3_1 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints3_1 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints3_1.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints3_1.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints3_1.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints3_1.gridheight = 1;
					nonOverlappingMarkersPanelConstraints3_1.gridx = 0;
					nonOverlappingMarkersPanelConstraints3_1.gridy = 0;
					nonOverlappingMarkersPanel3_1.setLayout(nonOverlappingMarkersPanelLayout3_1);
					nonOverlappingMarkersPanel3_2.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout3_2 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints3_2 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints3_2.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints3_2.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints3_2.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints3_2.gridheight = 1;
					nonOverlappingMarkersPanelConstraints3_2.gridx = 0;
					nonOverlappingMarkersPanelConstraints3_2.gridy = 0;
					nonOverlappingMarkersPanel3_2.setLayout(nonOverlappingMarkersPanelLayout3_2);
					JPanel nonOverlappingMarkersPanel4_1 = new JPanel(), nonOverlappingMarkersPanel4_2 = new JPanel();
					nonOverlappingMarkersPanel4_1.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout4_1 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints4_1 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints4_1.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints4_1.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints4_1.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints4_1.gridheight = 1;
					nonOverlappingMarkersPanelConstraints4_1.gridx = 0;
					nonOverlappingMarkersPanelConstraints4_1.gridy = 0;
					nonOverlappingMarkersPanel4_1.setLayout(nonOverlappingMarkersPanelLayout4_1);
					nonOverlappingMarkersPanel4_2.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout4_2 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints4_2 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints4_2.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints4_2.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints4_2.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints4_2.gridheight = 1;
					nonOverlappingMarkersPanelConstraints4_2.gridx = 0;
					nonOverlappingMarkersPanelConstraints4_2.gridy = 0;
					nonOverlappingMarkersPanel4_2.setLayout(nonOverlappingMarkersPanelLayout4_2);
					JPanel nonOverlappingMarkersPanel5_1 = new JPanel(), nonOverlappingMarkersPanel5_2 = new JPanel();
					nonOverlappingMarkersPanel5_1.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout5_1 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints5_1 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints5_1.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints5_1.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints5_1.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints5_1.gridheight = 1;
					nonOverlappingMarkersPanelConstraints5_1.gridx = 0;
					nonOverlappingMarkersPanelConstraints5_1.gridy = 0;
					nonOverlappingMarkersPanel5_1.setLayout(nonOverlappingMarkersPanelLayout5_1);
					nonOverlappingMarkersPanel5_2.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout5_2 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints5_2 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints5_2.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints5_2.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints5_2.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints5_2.gridheight = 1;
					nonOverlappingMarkersPanelConstraints5_2.gridx = 0;
					nonOverlappingMarkersPanelConstraints5_2.gridy = 0;
					nonOverlappingMarkersPanel5_2.setLayout(nonOverlappingMarkersPanelLayout5_2);
					JPanel nonOverlappingMarkersPanel6_1 = new JPanel(), nonOverlappingMarkersPanel6_2 = new JPanel();
					nonOverlappingMarkersPanel6_1.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout6_1 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints6_1 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints6_1.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints6_1.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints6_1.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints6_1.gridheight = 1;
					nonOverlappingMarkersPanelConstraints6_1.gridx = 0;
					nonOverlappingMarkersPanelConstraints6_1.gridy = 0;
					nonOverlappingMarkersPanel6_1.setLayout(nonOverlappingMarkersPanelLayout6_1);
					nonOverlappingMarkersPanel6_2.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout6_2 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints6_2 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints6_2.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints6_2.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints6_2.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints6_2.gridheight = 1;
					nonOverlappingMarkersPanelConstraints6_2.gridx = 0;
					nonOverlappingMarkersPanelConstraints6_2.gridy = 0;
					nonOverlappingMarkersPanel6_2.setLayout(nonOverlappingMarkersPanelLayout6_2);
					JPanel nonOverlappingMarkersPanel7_1 = new JPanel(), nonOverlappingMarkersPanel7_2 = new JPanel();
					nonOverlappingMarkersPanel7_1.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout7_1 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints7_1 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints7_1.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints7_1.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints7_1.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints7_1.gridheight = 1;
					nonOverlappingMarkersPanelConstraints7_1.gridx = 0;
					nonOverlappingMarkersPanelConstraints7_1.gridy = 0;
					nonOverlappingMarkersPanel7_1.setLayout(nonOverlappingMarkersPanelLayout7_1);
					nonOverlappingMarkersPanel7_2.setBorder(BorderFactory.createTitledBorder(""));
					GridBagLayout nonOverlappingMarkersPanelLayout7_2 = new GridBagLayout();
					GridBagConstraints nonOverlappingMarkersPanelConstraints7_2 = new GridBagConstraints();
					nonOverlappingMarkersPanelConstraints7_2.anchor = GridBagConstraints.NORTHWEST;
					nonOverlappingMarkersPanelConstraints7_2.fill = GridBagConstraints.HORIZONTAL;
					nonOverlappingMarkersPanelConstraints7_2.gridwidth = 1;
					nonOverlappingMarkersPanelConstraints7_2.gridheight = 1;
					nonOverlappingMarkersPanelConstraints7_2.gridx = 0;
					nonOverlappingMarkersPanelConstraints7_2.gridy = 0;
					nonOverlappingMarkersPanel7_2.setLayout(nonOverlappingMarkersPanelLayout7_2);


					nonOverlappingMarkersPanel1_1.add(marker1Sentence,nonOverlappingMarkersPanelConstraints1_1);
					nonOverlappingMarkersPanelConstraints1_1.gridy++;

					nonOverlappingMarkersPanel1_2.add(marker1RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
					nonOverlappingMarkersPanelConstraints1_2.gridx++;
					nonOverlappingMarkersPanel1_2.add(marker2RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
					nonOverlappingMarkersPanelConstraints1_2.gridx++;
					if(numOfObjectAssociatedMarkers>2) {
						nonOverlappingMarkersPanel1_2.add(marker3RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfObjectAssociatedMarkers>3) {
						nonOverlappingMarkersPanel1_2.add(marker4RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfObjectAssociatedMarkers>4) {
						nonOverlappingMarkersPanel1_2.add(marker5RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfObjectAssociatedMarkers>5) {
						nonOverlappingMarkersPanel1_2.add(marker6RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfObjectAssociatedMarkers>6) {
						nonOverlappingMarkersPanel1_2.add(marker7RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					nonOverlappingMarkersPanelConstraints1_2.gridy++;
					nonOverlappingMarkersPanelConstraints1_2.gridx=0;


					nonOverlappingMarkersPanel2_1.add(marker2Sentence,nonOverlappingMarkersPanelConstraints2_1);
					nonOverlappingMarkersPanelConstraints2_1.gridy++;

					nonOverlappingMarkersPanel2_2.add(marker1RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
					nonOverlappingMarkersPanelConstraints2_1.gridx++;
					nonOverlappingMarkersPanel2_2.add(marker2RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
					nonOverlappingMarkersPanelConstraints2_1.gridx++;
					if(numOfObjectAssociatedMarkers>2) {
						nonOverlappingMarkersPanel2_2.add(marker3RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfObjectAssociatedMarkers>3) {
						nonOverlappingMarkersPanel2_2.add(marker4RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfObjectAssociatedMarkers>4) {
						nonOverlappingMarkersPanel2_2.add(marker5RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfObjectAssociatedMarkers>5) {
						nonOverlappingMarkersPanel2_2.add(marker6RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfObjectAssociatedMarkers>6) {
						nonOverlappingMarkersPanel2_2.add(marker7RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					nonOverlappingMarkersPanelConstraints2_1.gridy++;
					nonOverlappingMarkersPanelConstraints2_1.gridx=0;

					if(numOfObjectAssociatedMarkers>2) {
						nonOverlappingMarkersPanel3_1.add(marker3Sentence,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridy++;

						nonOverlappingMarkersPanel3_2.add(marker1RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridx++;
						nonOverlappingMarkersPanel3_2.add(marker2RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridx++;
						nonOverlappingMarkersPanel3_2.add(marker3RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridx++;
						if(numOfObjectAssociatedMarkers>3) {
							nonOverlappingMarkersPanel3_2.add(marker4RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						if(numOfObjectAssociatedMarkers>4) {
							nonOverlappingMarkersPanel3_2.add(marker5RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						if(numOfObjectAssociatedMarkers>5) {
							nonOverlappingMarkersPanel3_2.add(marker6RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						if(numOfObjectAssociatedMarkers>6) {
							nonOverlappingMarkersPanel3_2.add(marker7RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints3_1.gridy++;
						nonOverlappingMarkersPanelConstraints3_1.gridx=0;
					}

					if(numOfObjectAssociatedMarkers>3) {
						nonOverlappingMarkersPanel4_1.add(marker4Sentence,nonOverlappingMarkersPanelConstraints4_1);
						nonOverlappingMarkersPanelConstraints4_1.gridy++;

						nonOverlappingMarkersPanel4_2.add(marker1RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
						nonOverlappingMarkersPanelConstraints4_1.gridx++;
						nonOverlappingMarkersPanel4_2.add(marker2RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
						nonOverlappingMarkersPanelConstraints4_1.gridx++;
						nonOverlappingMarkersPanel4_2.add(marker3RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
						nonOverlappingMarkersPanelConstraints4_1.gridx++;
						nonOverlappingMarkersPanel4_2.add(marker4RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
						nonOverlappingMarkersPanelConstraints4_1.gridx++;
						if(numOfObjectAssociatedMarkers>4) {
							nonOverlappingMarkersPanel4_2.add(marker5RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
							nonOverlappingMarkersPanelConstraints4_1.gridx++;
						}
						if(numOfObjectAssociatedMarkers>5) {
							nonOverlappingMarkersPanel4_2.add(marker6RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
							nonOverlappingMarkersPanelConstraints4_1.gridx++;
						}
						if(numOfObjectAssociatedMarkers>6) {
							nonOverlappingMarkersPanel4_2.add(marker7RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
							nonOverlappingMarkersPanelConstraints4_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints4_1.gridy++;
						nonOverlappingMarkersPanelConstraints4_1.gridx=0;
					}

					if(numOfObjectAssociatedMarkers>4) {
						nonOverlappingMarkersPanel5_1.add(marker5Sentence,nonOverlappingMarkersPanelConstraints5_1);
						nonOverlappingMarkersPanelConstraints5_1.gridy++;

						nonOverlappingMarkersPanel5_2.add(marker1RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
						nonOverlappingMarkersPanelConstraints5_1.gridx++;
						nonOverlappingMarkersPanel5_2.add(marker2RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
						nonOverlappingMarkersPanelConstraints5_1.gridx++;
						nonOverlappingMarkersPanel5_2.add(marker3RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
						nonOverlappingMarkersPanelConstraints5_1.gridx++;
						nonOverlappingMarkersPanel5_2.add(marker4RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
						nonOverlappingMarkersPanelConstraints5_1.gridx++;
						nonOverlappingMarkersPanel5_2.add(marker5RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
						nonOverlappingMarkersPanelConstraints5_1.gridx++;
						if(numOfObjectAssociatedMarkers>5) {
							nonOverlappingMarkersPanel5_2.add(marker6RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
							nonOverlappingMarkersPanelConstraints5_1.gridx++;
						}
						if(numOfObjectAssociatedMarkers>6) {
							nonOverlappingMarkersPanel5_2.add(marker7RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
							nonOverlappingMarkersPanelConstraints5_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints5_1.gridy++;
						nonOverlappingMarkersPanelConstraints5_1.gridx=0;
					}

					if(numOfObjectAssociatedMarkers>5) {
						nonOverlappingMarkersPanel6_1.add(marker6Sentence,nonOverlappingMarkersPanelConstraints6_1);
						nonOverlappingMarkersPanelConstraints6_1.gridy++;

						nonOverlappingMarkersPanel6_2.add(marker1RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
						nonOverlappingMarkersPanelConstraints6_1.gridx++;
						nonOverlappingMarkersPanel6_2.add(marker2RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
						nonOverlappingMarkersPanelConstraints6_1.gridx++;
						nonOverlappingMarkersPanel6_2.add(marker3RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
						nonOverlappingMarkersPanelConstraints6_1.gridx++;
						nonOverlappingMarkersPanel6_2.add(marker4RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
						nonOverlappingMarkersPanelConstraints6_1.gridx++;
						nonOverlappingMarkersPanel6_2.add(marker5RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
						nonOverlappingMarkersPanelConstraints6_1.gridx++;
						nonOverlappingMarkersPanel6_2.add(marker6RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
						nonOverlappingMarkersPanelConstraints6_1.gridx++;
						if(numOfObjectAssociatedMarkers>6) {
							nonOverlappingMarkersPanel6_2.add(marker7RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
							nonOverlappingMarkersPanelConstraints6_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints6_1.gridy++;
						nonOverlappingMarkersPanelConstraints6_1.gridx=0;
					}

					if(numOfObjectAssociatedMarkers>6) {
						nonOverlappingMarkersPanel7_1.add(marker7Sentence,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridy++;

						nonOverlappingMarkersPanel7_2.add(marker1RadioButton_7,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridx++;
						nonOverlappingMarkersPanel7_2.add(marker2RadioButton_7,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridx++;
						nonOverlappingMarkersPanel7_2.add(marker3RadioButton_7,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridx++;
						nonOverlappingMarkersPanel7_2.add(marker4RadioButton_7,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridx++;
						nonOverlappingMarkersPanel7_2.add(marker5RadioButton_7,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridx++;
						nonOverlappingMarkersPanel7_2.add(marker6RadioButton_7,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridx++;
						nonOverlappingMarkersPanel7_2.add(marker7RadioButton_7,nonOverlappingMarkersPanelConstraints7_1);
						nonOverlappingMarkersPanelConstraints7_1.gridx++;
						nonOverlappingMarkersPanelConstraints7_1.gridy++;
						nonOverlappingMarkersPanelConstraints7_1.gridx=0;
					}

					GenericDialogPlus gd2 = new GenericDialogPlus("Marker incompatibilities");
					switch (numOfObjectAssociatedMarkers) {
					case 2:
						gd2.addComponent(nonOverlappingMarkersPanel1_1);gd2.addComponent(nonOverlappingMarkersPanel1_2);
						gd2.addComponent(nonOverlappingMarkersPanel2_1);gd2.addComponent(nonOverlappingMarkersPanel2_2);
						break;
					case 3:
						gd2.addComponent(nonOverlappingMarkersPanel1_1);gd2.addComponent(nonOverlappingMarkersPanel1_2);
						gd2.addComponent(nonOverlappingMarkersPanel2_1);gd2.addComponent(nonOverlappingMarkersPanel2_2);
						gd2.addComponent(nonOverlappingMarkersPanel3_1);gd2.addComponent(nonOverlappingMarkersPanel3_2);
						break;
					case 4:
						gd2.addComponent(nonOverlappingMarkersPanel1_1);gd2.addComponent(nonOverlappingMarkersPanel1_2);
						gd2.addComponent(nonOverlappingMarkersPanel2_1);gd2.addComponent(nonOverlappingMarkersPanel2_2);
						gd2.addComponent(nonOverlappingMarkersPanel3_1);gd2.addComponent(nonOverlappingMarkersPanel3_2);
						gd2.addComponent(nonOverlappingMarkersPanel4_1);gd2.addComponent(nonOverlappingMarkersPanel4_2);
						break;
					case 5:
						gd2.addComponent(nonOverlappingMarkersPanel1_1);gd2.addComponent(nonOverlappingMarkersPanel1_2);
						gd2.addComponent(nonOverlappingMarkersPanel2_1);gd2.addComponent(nonOverlappingMarkersPanel2_2);
						gd2.addComponent(nonOverlappingMarkersPanel3_1);gd2.addComponent(nonOverlappingMarkersPanel3_2);
						gd2.addComponent(nonOverlappingMarkersPanel4_1);gd2.addComponent(nonOverlappingMarkersPanel4_2);
						gd2.addComponent(nonOverlappingMarkersPanel5_1);gd2.addComponent(nonOverlappingMarkersPanel5_2);
						break;
					case 6:
						gd2.addComponent(nonOverlappingMarkersPanel1_1);gd2.addComponent(nonOverlappingMarkersPanel1_2);
						gd2.addComponent(nonOverlappingMarkersPanel2_1);gd2.addComponent(nonOverlappingMarkersPanel2_2);
						gd2.addComponent(nonOverlappingMarkersPanel3_1);gd2.addComponent(nonOverlappingMarkersPanel3_2);
						gd2.addComponent(nonOverlappingMarkersPanel4_1);gd2.addComponent(nonOverlappingMarkersPanel4_2);
						gd2.addComponent(nonOverlappingMarkersPanel5_1);gd2.addComponent(nonOverlappingMarkersPanel5_2);
						gd2.addComponent(nonOverlappingMarkersPanel6_1);gd2.addComponent(nonOverlappingMarkersPanel6_2);
						break;
					case 7:
						gd2.addComponent(nonOverlappingMarkersPanel1_1);gd2.addComponent(nonOverlappingMarkersPanel1_2);
						gd2.addComponent(nonOverlappingMarkersPanel2_1);gd2.addComponent(nonOverlappingMarkersPanel2_2);
						gd2.addComponent(nonOverlappingMarkersPanel3_1);gd2.addComponent(nonOverlappingMarkersPanel3_2);
						gd2.addComponent(nonOverlappingMarkersPanel4_1);gd2.addComponent(nonOverlappingMarkersPanel4_2);
						gd2.addComponent(nonOverlappingMarkersPanel5_1);gd2.addComponent(nonOverlappingMarkersPanel5_2);
						gd2.addComponent(nonOverlappingMarkersPanel6_1);gd2.addComponent(nonOverlappingMarkersPanel6_2);
						gd2.addComponent(nonOverlappingMarkersPanel7_1);gd2.addComponent(nonOverlappingMarkersPanel7_2);
						break;
					default:
						break;
					}

					if(markerProcessingBatchProcess) {
						gd2.showDialog();

						if(gd2.wasCanceled()) {
							return;
						}
					}
				}

				/** combination of markers */
				if(nbCombinations>0){
					JLabel label4 = new JLabel("Do you want to add the previously defined combination of markers?");
					scale(label4);
					switch ( JOptionPane.showConfirmDialog( null, label4, "Marker combination", JOptionPane.YES_NO_OPTION ) )
					{
					case JOptionPane.YES_OPTION:
						break;
					case JOptionPane.NO_OPTION:
						nbCombinations = 0;
						combinationNames = new String[64];
						markerCombinations = new short[64][7];
						break;
					}

				}

				boolean markerCombination = true;
				if(nbCombinations==0){
					while(markerCombination){
						JTextArea markerCombinationTextField = new JTextArea();
						scale(markerCombinationTextField);
						markerCombinationTextField.setText("");
						JLabel label5 = new JLabel("Do you want to add a combination of markers?");
						scale(label5);
						switch ( JOptionPane.showConfirmDialog( null, label5, "Marker combination", JOptionPane.YES_NO_OPTION ) )
						{
						case JOptionPane.YES_OPTION:
							/** buttons */
							JTextArea markerCombinationQuestion = new JTextArea("What is the name of this marker combination?");
							scale(markerCombinationQuestion);
							markerCombinationQuestion.setEditable(false);

							JPanel markerCombinationPanel = new JPanel();
							markerCombinationPanel.setBorder(BorderFactory.createTitledBorder(""));
							GridBagLayout markerCombinationPanelLayout = new GridBagLayout();
							GridBagConstraints markerCombinationPanelConstraints = new GridBagConstraints();
							markerCombinationPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
							markerCombinationPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
							markerCombinationPanelConstraints.gridwidth = 1;
							markerCombinationPanelConstraints.gridheight = 1;
							markerCombinationPanelConstraints.gridx = 0;
							markerCombinationPanelConstraints.gridy = 0;
							markerCombinationPanel.setLayout(markerCombinationPanelLayout);

							markerCombinationPanel.add(markerCombinationQuestion,markerCombinationPanelConstraints);
							markerCombinationPanelConstraints.gridy++;
							markerCombinationTextField.setPreferredSize( new Dimension( 50, 24 ) );
							markerCombinationPanel.add(markerCombinationTextField,markerCombinationPanelConstraints);

							GenericDialogPlus gdMarkerCombination = new GenericDialogPlus("Marker combination");
							gdMarkerCombination.addComponent(markerCombinationPanel);
							gdMarkerCombination.showDialog();

							if (gdMarkerCombination.wasCanceled())
								markerCombination = false;

							break;
						case JOptionPane.NO_OPTION:
							markerCombination = false;
							break;
						}
						if(markerCombination){

							JRadioButton marker1RadioButton = new JRadioButton("Marker 1");
							scale(marker1RadioButton);
							marker1RadioButton.setSelected(false);
							JRadioButton marker2RadioButton = new JRadioButton("Marker 2");
							scale(marker2RadioButton);
							marker2RadioButton.setSelected(false);
							JRadioButton marker3RadioButton = new JRadioButton("Marker 3");
							scale(marker3RadioButton);
							marker3RadioButton.setSelected(false);
							JRadioButton marker4RadioButton = new JRadioButton("Marker 4");
							scale(marker4RadioButton);
							marker4RadioButton.setSelected(false);
							JRadioButton marker5RadioButton = new JRadioButton("Marker 5");
							scale(marker5RadioButton);
							marker5RadioButton.setSelected(false);
							JRadioButton marker6RadioButton = new JRadioButton("Marker 6");
							scale(marker6RadioButton);
							marker6RadioButton.setSelected(false);
							JRadioButton marker7RadioButton = new JRadioButton("Marker 7");
							scale(marker7RadioButton);
							marker7RadioButton.setSelected(false);

							JPanel currentmarkersPanel = new JPanel();
							currentmarkersPanel.setBorder(BorderFactory.createTitledBorder(""));
							GridBagLayout currentmarkersPanelLayout = new GridBagLayout();
							GridBagConstraints currentmarkersPanelConstraints = new GridBagConstraints();
							currentmarkersPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
							currentmarkersPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
							currentmarkersPanelConstraints.gridwidth = 1;
							currentmarkersPanelConstraints.gridheight = 1;
							currentmarkersPanelConstraints.gridx = 0;
							currentmarkersPanelConstraints.gridy = 0;
							currentmarkersPanel.setLayout(currentmarkersPanelLayout);
							currentmarkersPanel.add(marker1RadioButton,currentmarkersPanelConstraints);
							currentmarkersPanelConstraints.gridx++;
							if(numOfObjectAssociatedMarkers>1) {
								currentmarkersPanel.add(marker2RadioButton,currentmarkersPanelConstraints);
								currentmarkersPanelConstraints.gridx++;
							}
							if(numOfObjectAssociatedMarkers>2) {
								currentmarkersPanel.add(marker3RadioButton,currentmarkersPanelConstraints);
								currentmarkersPanelConstraints.gridx++;
							}
							if(numOfObjectAssociatedMarkers>3) {
								currentmarkersPanel.add(marker4RadioButton,currentmarkersPanelConstraints);
								currentmarkersPanelConstraints.gridx++;
							}
							if(numOfObjectAssociatedMarkers>4) {
								currentmarkersPanel.add(marker5RadioButton,currentmarkersPanelConstraints);
								currentmarkersPanelConstraints.gridx++;
							}
							if(numOfObjectAssociatedMarkers>5) {
								currentmarkersPanel.add(marker6RadioButton,currentmarkersPanelConstraints);
								currentmarkersPanelConstraints.gridx++;
							}
							if(numOfObjectAssociatedMarkers>6) {
								currentmarkersPanel.add(marker7RadioButton,currentmarkersPanelConstraints);
								currentmarkersPanelConstraints.gridx++;
							}

							GenericDialogPlus gdMarkerCombinationChoice = new GenericDialogPlus("Marker combination");
							gdMarkerCombinationChoice.addMessage("Which markers define this combination?");
							gdMarkerCombinationChoice.addComponent(currentmarkersPanel);
							gdMarkerCombinationChoice.showDialog();

							if (gdMarkerCombinationChoice.wasCanceled())
								markerCombination = false;
							else{
								combinationNames[nbCombinations] = markerCombinationTextField.getText();
								if(marker1RadioButton.isSelected()){markerCombinations[nbCombinations][0] = 1;}
								else{markerCombinations[nbCombinations][0] = 0;}
								if(marker2RadioButton.isSelected()){markerCombinations[nbCombinations][1] = 1;}
								else{markerCombinations[nbCombinations][1] = 0;}
								if(marker3RadioButton.isSelected()){markerCombinations[nbCombinations][2] = 1;}
								else{markerCombinations[nbCombinations][2] = 0;}
								if(marker4RadioButton.isSelected()){markerCombinations[nbCombinations][3] = 1;}
								else{markerCombinations[nbCombinations][3] = 0;}
								if(marker5RadioButton.isSelected()){markerCombinations[nbCombinations][4] = 1;}
								else{markerCombinations[nbCombinations][4] = 0;}
								if(marker6RadioButton.isSelected()){markerCombinations[nbCombinations][5] = 1;}
								else{markerCombinations[nbCombinations][5] = 0;}
								if(marker7RadioButton.isSelected()){markerCombinations[nbCombinations][6] = 1;}
								else{markerCombinations[nbCombinations][6] = 0;}
								nbCombinations++;
							}

						}
					}
				}
			}

			// store features for training if any
			storeFeaturesForTraining();
			//	storing all information needed to identify objects associated markers with thresholding
			byte[] markerCellcompartmentMem = new byte[]{0,0,0,0,0,0,0}; 
			byte[] channelsForObjectAssociatedMarkersMem = new byte[]{-1,-1,-1,-1,-1,-1,-1};
			int[][] thresholdsForObjectAssociatedMarkersMem = new int[][]{{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1}};
			byte[] methodToIdentifyObjectAssociatedMarkersMem = new byte[]{0,0,0,0,0,0,0};
			List<double[]> [] featuresForEachMarkerMem = new ArrayList[MAX_NUM_MARKERS];

			for(int p=0;p<numOfObjectAssociatedMarkers;p++) {
				markerCellcompartmentMem[p] = markerCellcompartment[p];
				channelsForObjectAssociatedMarkersMem[p] = channelsForObjectAssociatedMarkers[p];
				thresholdsForObjectAssociatedMarkersMem[p][0] = thresholdsForObjectAssociatedMarkers[p][0];
				thresholdsForObjectAssociatedMarkersMem[p][1] = thresholdsForObjectAssociatedMarkers[p][1];
				methodToIdentifyObjectAssociatedMarkersMem[p] = methodToIdentifyObjectAssociatedMarkers[p];
				featuresForEachMarkerMem[p] = featuresForEachMarker[p];
			}
						
			
			// batch process
			for (File imageFileEntry : imageFile.listFiles()) {
				if (!imageFileEntry.isDirectory()) {
					String[] currentImageFile = imageFileEntry.getName().split("\\.");
					if (currentImageFile.length > 1) {
						if ((currentImageFile[1].equals("tiff")) || (currentImageFile[1].equals("tif")) || (currentImageFile[1].equals("png"))){
							String currentSegmentationFile = new String();
							for (File segmentationFileEntry : segmentationFile.listFiles()) {
								String[] currentSegmentationFileTest = segmentationFileEntry.getName().split("\\.");
								if(currentSegmentationFileTest[0].equals(currentImageFile[0])) {currentSegmentationFile = segmentationFileEntry.getName();}
							}
							win.close();

							Opener opener = new Opener();
							displayImage = opener.openImage(imageFolder+imageFileEntry.getName());

							int[] dims = displayImage.getDimensions();
							if((dims[2]==1)&&(dims[3]==1)&&(dims[4]==1)) {
								ImageConverter ic = new ImageConverter(displayImage);
								ic.convertToRGB();
							}

							if(displayImage.getType()==4) {
								displayImage = CompositeConverter.makeComposite(displayImage);
								dims = displayImage.getDimensions();
							}

							if(dims[2]==1) {
								if((dims[3]>1)&&(dims[4]==1)) {
									displayImage = HyperStackConverter.toHyperStack(displayImage, dims[3], 1, 1);
								}
								if((dims[4]>1)&&(dims[3]==1)) {
									displayImage = HyperStackConverter.toHyperStack(displayImage, dims[4], 1, 1);
								}
								dims = displayImage.getDimensions();
							}

							numOfChannels = (byte)dims[2];

							if(numOfChannels>7) {
								IJ.showMessage("Too many channels", "Images cannot exceed 7 channels");
								return;
							}
							if((dims[3]>1)||(dims[4]>1)) {
								IJ.showMessage("2D image", "Only 2D multi-channel images are accepted");
								return;
							}

							// reinitialization of objects and areas
							roiFlag = new short [displayImage.getWidth()][displayImage.getHeight()][3];
							for(int y=0; y<displayImage.getHeight(); y++)
							{
								for(int x=0; x<displayImage.getWidth(); x++)
								{
									roiFlag[x][y][0] = -1;
									roiFlag[x][y][1] = -1;
									roiFlag[x][y][2] = -1;
								}
							}
							for(int c=0;c<numOfAreas;c++) {
								areasInEachClass[c] = null;
							}
							areasInEachClass[0] = new ArrayList<Point[]>();
							numOfAreas = 1;
							// update flags for cell compartment computation
							nuclearComponentFlag = false;
							innerNuclearComponentFlag = false;
							membranarComponentFlag = false;
							cytoplasmicComponentFlag = false;
							rt_nuclearML_flag = false;

							ImagePlus segmentedImage = opener.openImage(segmentationFolder+currentSegmentationFile);
							int actualNumOfObjectAssociatedMarkers = numOfObjectAssociatedMarkers;
							currentObjectAssociatedMarker = -1;
							initializeMarkerButtons();
							
							if(areaBatchProcess){
								overlay = new Overlay();
								markersOverlay = new Overlay();

								String currentAreaAssociatedMarkerFile = new String();
								for (File areaAssociatedMarkerFileEntry : areaAssociatedMarkerFile.listFiles()) {
									String[] currentMarkerFileTest = areaAssociatedMarkerFileEntry.getName().split("\\.");
									if(currentMarkerFileTest[0].equals(currentImageFile[0])) {currentAreaAssociatedMarkerFile = areaAssociatedMarkerFileEntry.getName();}
								}
								ImagePlus areaAssociatedMarkerImage = opener.openImage(areaFolder+currentAreaAssociatedMarkerFile);
								loadAreas(areaAssociatedMarkerImage);

								final ResultsTable areaRt = new ResultsTable();
								areaRt.incrementCounter();
								for(int i=0;i<numOfAreas;i++){
									int totalNbPixels=0;
									for(int u=0;u<areasInEachClass[i].size();u++){
										totalNbPixels += areasInEachClass[i].get(u).length;
									}
									areaRt.addValue("Region" + (i+1), totalNbPixels);
								}
								areaRt.save(measurementsFolder+currentSegmentationFile.split("\\.")[0]+"_areas.txt");
							}
							loadNucleiSegmentations(segmentedImage);
							if(objectBatchProcess){
								if(markerProcessingBatchProcess) {
									for(int p=0;p<actualNumOfObjectAssociatedMarkers;p++) {
										addNewMarker();
										
										markerCellcompartment[p] = markerCellcompartmentMem[p];
										channelsForObjectAssociatedMarkers[p] = channelsForObjectAssociatedMarkersMem[p];
										thresholdsForObjectAssociatedMarkers[p][0] = thresholdsForObjectAssociatedMarkersMem[p][0];
										thresholdsForObjectAssociatedMarkers[p][1] = thresholdsForObjectAssociatedMarkersMem[p][1];
										featuresForEachMarker[p] = featuresForEachMarkerMem[p];
										methodToIdentifyObjectAssociatedMarkers[p] = methodToIdentifyObjectAssociatedMarkersMem[p];

										updateAnnotateObjectAssociatedMarker(numOfObjectAssociatedMarkers-1,false);
										if(methodToIdentifyObjectAssociatedMarkers[p]==1){
											if(channelsForObjectAssociatedMarkers[p]>(-1)) {
												List<Polygon> [] cellComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];
												for(int i=0;i<numOfClasses;i++) {
													cellComponentInEachClass[i] = new ArrayList<Polygon>();
												}
												for(int i=0;i<numOfClasses;i++) {
													for(int j=0;j<objectsInEachClass[i].size();j++) {
														Polygon fp = new Polygon();
														cellComponentInEachClass[i].add(fp);
													}
												}

												if(markerCellcompartment[p]==0) {
													if(!nuclearComponentFlag){
														computeNuclearComponent();
														nuclearComponentFlag = true;
													}
													for(int i=0;i<numOfClasses;i++) {
														for(int y=0;y<displayImage.getHeight();y++) {
															for(int x=0;x<displayImage.getWidth();x++) {
																if(nuclearComponent[i][x][y]>0) {
																	cellComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
																}
															}
														}
													}
												}
												else if(markerCellcompartment[p]==1) {
													if(!nuclearComponentFlag){
														computeNuclearComponent();
														nuclearComponentFlag = true;
													}
													if(!innerNuclearComponentFlag){
														computeInnerNuclearComponent();
														innerNuclearComponentFlag = true;
													}
													if(!membranarComponentFlag){
														computeMembranarComponent();
														membranarComponentFlag = true;
													}
													for(int i=0;i<numOfClasses;i++) {
														for(int y=0;y<displayImage.getHeight();y++) {
															for(int x=0;x<displayImage.getWidth();x++) {
																if(membranarComponent[i][x][y]>0) {
																	cellComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
																}
															}
														}
													}
												}
												else if(markerCellcompartment[p]==2) {
													if(!nuclearComponentFlag){
														computeNuclearComponent();
														nuclearComponentFlag = true;
													}
													if(!innerNuclearComponentFlag){
														computeInnerNuclearComponent();
														innerNuclearComponentFlag = true;
													}
													if(!cytoplasmicComponentFlag){
														computeCytoplasmicComponent();
														cytoplasmicComponentFlag = true;
													}
													for(int i=0;i<numOfClasses;i++) {
														for(int y=0;y<displayImage.getHeight();y++) {
															for(int x=0;x<displayImage.getWidth();x++) {
																if(cytoplasmicComponent[i][x][y]>0) {
																	cellComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
																}
															}
														}
													}
												}
												chosenChannelForObjectAssociatedMarker = channelsForObjectAssociatedMarkers[p];
												areaThresholdingScrollBar.setValue(thresholdsForObjectAssociatedMarkers[p][0]);
												intensityThresholdingForObjectAssociatedMarkerScrollBar.setValue(thresholdsForObjectAssociatedMarkers[p][1]);
												computeIntensityThresholdForEachObject(cellComponentInEachClass);
												roiActivationAndDeactivationBasedOnThresholding();
											}
											removeMarkersFromOverlay();
											updateModeRadioButtons(1);
										}
										else if(methodToIdentifyObjectAssociatedMarkers[p]==2){
											train(p);
											removeMarkersFromOverlay();
											updateModeRadioButtons(1);
										}
									}
									// incompatibilities between markers
									if(numOfObjectAssociatedMarkers>1) {
										if(marker2RadioButton_1.isSelected()) {removeIncompatibility(0,1);}
										if(marker3RadioButton_1.isSelected()) {removeIncompatibility(0,2);}
										if(marker4RadioButton_1.isSelected()) {removeIncompatibility(0,3);}
										if(marker5RadioButton_1.isSelected()) {removeIncompatibility(0,4);}
										if(marker6RadioButton_1.isSelected()) {removeIncompatibility(0,5);}
										if(marker7RadioButton_1.isSelected()) {removeIncompatibility(0,6);}
										if(marker1RadioButton_2.isSelected()) {removeIncompatibility(1,0);}
										if(marker3RadioButton_2.isSelected()) {removeIncompatibility(1,2);}
										if(marker4RadioButton_2.isSelected()) {removeIncompatibility(1,3);}
										if(marker5RadioButton_2.isSelected()) {removeIncompatibility(1,4);}
										if(marker6RadioButton_2.isSelected()) {removeIncompatibility(1,5);}
										if(marker7RadioButton_2.isSelected()) {removeIncompatibility(1,6);}
									}
									if(numOfObjectAssociatedMarkers>2) {
										if(marker1RadioButton_3.isSelected()) {removeIncompatibility(2,0);}
										if(marker2RadioButton_3.isSelected()) {removeIncompatibility(2,1);}
										if(marker4RadioButton_3.isSelected()) {removeIncompatibility(2,3);}
										if(marker5RadioButton_3.isSelected()) {removeIncompatibility(2,4);}
										if(marker6RadioButton_3.isSelected()) {removeIncompatibility(2,5);}
										if(marker7RadioButton_3.isSelected()) {removeIncompatibility(2,6);}
									}
									if(numOfObjectAssociatedMarkers>3) {
										if(marker1RadioButton_4.isSelected()) {removeIncompatibility(3,0);}
										if(marker2RadioButton_4.isSelected()) {removeIncompatibility(3,1);}
										if(marker3RadioButton_4.isSelected()) {removeIncompatibility(3,2);}
										if(marker5RadioButton_4.isSelected()) {removeIncompatibility(3,4);}
										if(marker6RadioButton_4.isSelected()) {removeIncompatibility(3,5);}
										if(marker7RadioButton_4.isSelected()) {removeIncompatibility(3,6);}
									}
									if(numOfObjectAssociatedMarkers>4) {
										if(marker1RadioButton_5.isSelected()) {removeIncompatibility(4,0);}
										if(marker2RadioButton_5.isSelected()) {removeIncompatibility(4,1);}
										if(marker3RadioButton_5.isSelected()) {removeIncompatibility(4,2);}
										if(marker4RadioButton_5.isSelected()) {removeIncompatibility(4,3);}
										if(marker6RadioButton_5.isSelected()) {removeIncompatibility(4,5);}
										if(marker7RadioButton_5.isSelected()) {removeIncompatibility(4,6);}
									}
									if(numOfObjectAssociatedMarkers>5) {
										if(marker1RadioButton_6.isSelected()) {removeIncompatibility(5,0);}
										if(marker2RadioButton_6.isSelected()) {removeIncompatibility(5,1);}
										if(marker3RadioButton_6.isSelected()) {removeIncompatibility(5,2);}
										if(marker4RadioButton_6.isSelected()) {removeIncompatibility(5,3);}
										if(marker5RadioButton_6.isSelected()) {removeIncompatibility(5,4);}
										if(marker7RadioButton_6.isSelected()) {removeIncompatibility(5,6);}
									}
									if(numOfObjectAssociatedMarkers>6) {
										if(marker1RadioButton_7.isSelected()) {removeIncompatibility(6,0);}
										if(marker2RadioButton_7.isSelected()) {removeIncompatibility(6,1);}
										if(marker3RadioButton_7.isSelected()) {removeIncompatibility(6,2);}
										if(marker4RadioButton_7.isSelected()) {removeIncompatibility(6,3);}
										if(marker5RadioButton_7.isSelected()) {removeIncompatibility(6,4);}
										if(marker6RadioButton_7.isSelected()) {removeIncompatibility(6,5);}
									}
									saveObjectAssociatedMarkerIdentifications(objectAssociatedMarkerFolder+currentSegmentationFile.split("\\.")[0]+".tiff");
								}
								else{
									String currentObjectAssociatedMarkerFile = new String();
									for (File objectAssociatedMarkerFileEntry : objectAssociatedMarkerFile.listFiles()) {
										String[] currentMarkerFileTest = objectAssociatedMarkerFileEntry.getName().split("\\.");
										if(currentMarkerFileTest[0].equals(currentImageFile[0])) {currentObjectAssociatedMarkerFile = objectAssociatedMarkerFileEntry.getName();}
									}
									ImagePlus objectAssociatedMarkerImage = opener.openImage(objectAssociatedMarkerFolder+currentObjectAssociatedMarkerFile);
									loadObjectAssociatedMarkerIdentifications(objectAssociatedMarkerImage);
								}
							}
							if(outputImageBatchProcess) {
								takeClassSnapshot(outputImageFolder+currentSegmentationFile.split("\\.")[0]+"_segmentation.tiff");
								if(objectBatchProcess&&areaBatchProcess){
									markerMeasurementsAndAllSnapshots(measurementsFolder+currentSegmentationFile.split("\\.")[0]+".txt", outputImageFolder+currentSegmentationFile.split("\\.")[0]+"_markers.tiff", nbCombinations, combinationNames, markerCombinations);
								}
								else if(objectBatchProcess){
									markerMeasurementsAndObjectSnapshots(measurementsFolder+currentSegmentationFile.split("\\.")[0]+".txt", outputImageFolder+currentSegmentationFile.split("\\.")[0]+"_markers.tiff", nbCombinations, combinationNames, markerCombinations);
								}
								else if(areaBatchProcess){
									markerMeasurementsAndAreaSnapshots(measurementsFolder+currentSegmentationFile.split("\\.")[0]+".txt", outputImageFolder+currentSegmentationFile.split("\\.")[0]+"_markers.tiff");
								}
							}
							else{
								markerMeasurements(measurementsFolder+currentSegmentationFile.split("\\.")[0]+".txt", nbCombinations, combinationNames, markerCombinations);
							}
						}
					}
				}
			}
		}
	}

	/** ask user to set intensity thresholding */ 
	private boolean addObjectAssociatedIntensityThresholdingWindow()
	{
		/** buttons */
		JTextArea intensityThresholdQuestion = new JTextArea("What is the intensity threshold?");
		scale(intensityThresholdQuestion);
		intensityThresholdQuestion.setEditable(false);
		JTextArea intensityThresholdTextField = new JTextArea();
		scale(intensityThresholdTextField);
		intensityThresholdTextField.setText("" + intensityThresholdingForObjectAssociatedMarkerScrollBar.getValue());

		JPanel thresholdingPanel = new JPanel();
		thresholdingPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout thresholdingPanelLayout = new GridBagLayout();
		GridBagConstraints thresholdingPanelConstraints = new GridBagConstraints();
		thresholdingPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		thresholdingPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		thresholdingPanelConstraints.gridwidth = 1;
		thresholdingPanelConstraints.gridheight = 1;
		thresholdingPanelConstraints.gridx = 0;
		thresholdingPanelConstraints.gridy = 0;
		thresholdingPanel.setLayout(thresholdingPanelLayout);

		thresholdingPanel.add(intensityThresholdQuestion,thresholdingPanelConstraints);
		thresholdingPanelConstraints.gridy++;
		intensityThresholdTextField.setPreferredSize( new Dimension( 50, 24 ) );
		thresholdingPanel.add(intensityThresholdTextField,thresholdingPanelConstraints);

		GenericDialogPlus gd = new GenericDialogPlus("Intensity threshold");
		gd.addComponent(thresholdingPanel);
		gd.showDialog();

		if (gd.wasCanceled())
			return false;

		// update cell compartment marker status
		int threshold = Integer.valueOf(intensityThresholdTextField.getText());
		if(threshold<0) {
			IJ.showMessage("The threshold must be positive");
			return false;}
		if(threshold>intensityThresholdingForObjectAssociatedMarkerScrollBar.getMaximum()) {
			IJ.showMessage("The threshold must be inferior than the maximum intensity");
			return false;}

		intensityThresholdingForObjectAssociatedMarkerScrollBar.setValue(threshold);
		intensityThresholdingForObjectAssociatedMarkerTextArea.setText("" + threshold);
		thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1][1] = threshold;

		return true;
	}
	/** ask user to set intensity thresholding */ 
	private boolean addAreaThresholdingWindow()
	{
		/** buttons */
		JTextArea areaThresholdQuestion = new JTextArea("What is the area threshold (%)?");
		scale(areaThresholdQuestion);
		areaThresholdQuestion.setEditable(false);
		JTextArea areaThresholdTextField = new JTextArea();
		scale(areaThresholdTextField);
		areaThresholdTextField.setText("" + areaThresholdingScrollBar.getValue());

		JPanel thresholdingPanel = new JPanel();
		thresholdingPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout thresholdingPanelLayout = new GridBagLayout();
		GridBagConstraints thresholdingPanelConstraints = new GridBagConstraints();
		thresholdingPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		thresholdingPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		thresholdingPanelConstraints.gridwidth = 1;
		thresholdingPanelConstraints.gridheight = 1;
		thresholdingPanelConstraints.gridx = 0;
		thresholdingPanelConstraints.gridy = 0;
		thresholdingPanel.setLayout(thresholdingPanelLayout);

		thresholdingPanel.add(areaThresholdQuestion,thresholdingPanelConstraints);
		thresholdingPanelConstraints.gridy++;
		areaThresholdTextField.setPreferredSize( new Dimension( 50, 24 ) );
		thresholdingPanel.add(areaThresholdTextField,thresholdingPanelConstraints);

		GenericDialogPlus gd = new GenericDialogPlus("Region threshold");
		gd.addComponent(thresholdingPanel);
		gd.showDialog();

		if (gd.wasCanceled())
			return false;

		// update cell compartment marker status
		int threshold = Integer.valueOf(areaThresholdTextField.getText());
		if(threshold<0) {
			IJ.showMessage("The threshold must be positive");
			return false;}
		if(threshold>100) {
			IJ.showMessage("The threshold must be inferior or equal to 100%");
			return false;}

		areaThresholdingScrollBar.setValue(threshold);
		areaThresholdingTextArea.setText("" + threshold);
		thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers-1][0] = threshold;

		return true;
	}
	/**
	 * Draw the objects outline on the display image
	 */
	private void drawNewObjectContour(Roi r, int classId)
	{
		Polygon outline = r.getPolygon();
		PolygonRoi displayedRoi = new PolygonRoi(outline, Roi.FREEROI);
		displayedRoi.setStrokeColor(colors[classColors[classId]]);
		overlay.add(displayedRoi);
		markersOverlay.add(displayedRoi);
	}

	private void drawNewObjectContour(int[] xPointsInit, int[] yPointsInit, int classId)
	{
		PointRoi pr = new PointRoi(xPointsInit, yPointsInit, xPointsInit.length);
		ShapeRoi roi = new ShapeRoi(pr);

		// add the roi to the overlay
		roi.setStrokeColor(colors[classColors[classId]]);
		overlay.add(roi);
		markersOverlay.add(roi);
	}
	/** draw new area */
	private void drawArea(Point[] pts,int areaId)
	{
		int[][] area = new int[displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<pts.length;i++){
			area[pts[i].x][pts[i].y] = 255;
		}
		ImageProcessor areaIP = new FloatProcessor(area);
		areaIP.setColorModel(areaColorModels[areaColors[areaId]]);
		ImageRoi roi = new ImageRoi(0, 0, areaIP);
		roi.setOpacity(0.2);
		roi.setZeroTransparent(true);
		overlay.add(roi);
		markersOverlay.add(roi);
	}
	/** draw new area */
	private void drawArea(Point[] pts,int areaId, Overlay outputOverlay)
	{
		int[][] area = new int[displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<pts.length;i++){
			area[pts[i].x][pts[i].y] = 255;
		}
		ImageProcessor areaIP = new FloatProcessor(area);
		areaIP.setColorModel(areaColorModels[areaColors[areaId]]);
		ImageRoi roi = new ImageRoi(0, 0, areaIP);
		roi.setOpacity(0.2);
		roi.setZeroTransparent(true);
		outputOverlay.add(roi);
	}
	/** draw new area */
	private void drawAreaForSnapshot(Point[] pts,int areaId, Overlay outputOverlay, int[][] markers_mask)
	{
		int[][] area = new int[displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<pts.length;i++){
			if(markers_mask[pts[i].x][pts[i].y]==0){
				area[pts[i].x][pts[i].y] = 255;
			}
		}
		ImageProcessor areaIP = new FloatProcessor(area);
		areaIP.setColorModel(areaColorModels[areaColors[areaId]]);
		ImageRoi roi = new ImageRoi(0, 0, areaIP);
		roi.setOpacity(0.2);
		roi.setZeroTransparent(true);
		outputOverlay.add(roi);
	}
	/**
	 * Remove objects
	 */
	private void removeRoi(int classId, int roiId, int overlayId)
	{
		objectsInEachClass[classId].remove(roiId);
		for(byte j=0;j<numOfObjectAssociatedMarkers;j++) {
			for(byte p=0;p<4;p++) {
				for(int i = 0; i < positiveNucleiForEachMarker[j][p].size(); i++) {
					if(positiveNucleiForEachMarker[j][p].get(i)>overlayId) {
						positiveNucleiForEachMarker[j][p].set(i, (short)(positiveNucleiForEachMarker[j][p].get(i)-1));
					}
					else{
						if(positiveNucleiForEachMarker[j][p].get(i)==overlayId) {
							positiveNucleiForEachMarker[j][p].remove(i);
							i--;
						}
					}
				}
			}
		}
		overlay.remove(overlayId);
		markersOverlay.remove(overlayId);
		for(int y=0; y<displayImage.getHeight(); y++)
		{
			for(int x=0; x<displayImage.getWidth(); x++)
			{
				if(roiFlag[x][y][0]==classId)
				{
					if(roiFlag[x][y][1]==roiId)
					{
						roiFlag[x][y][0] = -1;
						roiFlag[x][y][1] = -1;
						roiFlag[x][y][2] = -1;
					}
					else {
						if(roiFlag[x][y][1]>roiId)
						{
							roiFlag[x][y][1]--;
						}
					}
				}
				if(roiFlag[x][y][2]>overlayId)
				{
					roiFlag[x][y][2]--;
				}
				if(areaFlag[x][y][2]>overlayId)
				{
					areaFlag[x][y][2]--;
				}
			}
		}
	}
	/**
	 * Remove objects
	 */
	private void removeAreaRoi(int classId, int roiId, int overlayId)
	{
		areasInEachClass[classId].remove(roiId);
		overlay.remove(overlayId);
		markersOverlay.remove(overlayId);
		for(int y=0; y<displayImage.getHeight(); y++)
		{
			for(int x=0; x<displayImage.getWidth(); x++)
			{
				if(areaFlag[x][y][0]==classId)
				{
					if(areaFlag[x][y][1]==roiId)
					{
						areaFlag[x][y][0] = -1;
						areaFlag[x][y][1] = -1;
						areaFlag[x][y][2] = -1;
					}
					else {
						if(areaFlag[x][y][1]>roiId)
						{
							areaFlag[x][y][1]--;
						}
					}
				}
				if(areaFlag[x][y][2]>overlayId)
				{
					areaFlag[x][y][2]--;
				}
				if(roiFlag[x][y][2]>overlayId)
				{
					roiFlag[x][y][2]--;
				}
			}
		}
	}

	/**
	 * Remove objects
	 */
	private void removeObject()
	{
		//get selected region
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		// update flags for cell compartment computation
		nuclearComponentFlag = false;
		innerNuclearComponentFlag = false;
		membranarComponentFlag = false;
		cytoplasmicComponentFlag = false;
		rt_nuclearML_flag = false;
		
		displayImage.killRoi();

		Point[] pts = r.getContainedPoints();
		if(roiFlag[pts[0].x][pts[0].y][0]>(-1)) {
			int objectIdToRemove = roiFlag[pts[0].x][pts[0].y][1], objectClassToRemove = roiFlag[pts[0].x][pts[0].y][0], overlayIdToRemove = roiFlag[pts[0].x][pts[0].y][2];
			removeRoi(objectClassToRemove, objectIdToRemove, overlayIdToRemove);			
		}
		displayImage.updateAndDraw();
	}

	/**
	 * Merge objects
	 */
	private void mergeObjects()
	{
		//get selected region
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		// update flags for cell compartment computation
		nuclearComponentFlag = false;
		innerNuclearComponentFlag = false;
		membranarComponentFlag = false;
		cytoplasmicComponentFlag = false;
		rt_nuclearML_flag = false;
		
		displayImage.killRoi();

		Point[] pts = r.getContainedPoints();
		if(roiFlag[pts[0].x][pts[0].y][0]>(-1)) {
			if(firstObjectToMerge_class==-1) {
				firstObjectToMerge_class = roiFlag[pts[0].x][pts[0].y][0];
				firstObjectToMerge_classId = roiFlag[pts[0].x][pts[0].y][1];
				firstObjectToMerge_overlayId = roiFlag[pts[0].x][pts[0].y][2];
				overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(2);
			}
			else {
				if((roiFlag[pts[0].x][pts[0].y][0]==firstObjectToMerge_class)&&(roiFlag[pts[0].x][pts[0].y][1]==firstObjectToMerge_classId)&&(roiFlag[pts[0].x][pts[0].y][2]==firstObjectToMerge_overlayId)) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;
					firstObjectToMerge_classId = -1;
					firstObjectToMerge_overlayId = -1;
				}
				else {
					if(roiFlag[pts[0].x][pts[0].y][0]!=firstObjectToMerge_class) {
						IJ.showMessage("Merging problem", "Only two objects from the same class can be merged together.");
					}
					else {
						// copy rois to merge
						//Polygon r1 = objectsInEachClass[firstObjectToMerge_class].get(firstObjectToMerge_classId).getPolygon(),
						//	r2 = objectsInEachClass[firstObjectToMerge_class].get(roiFlag[pts[0].x][pts[0].y][1]).getPolygon();
						Point[] r1 = objectsInEachClass[firstObjectToMerge_class].get(firstObjectToMerge_classId),
								r2 = objectsInEachClass[firstObjectToMerge_class].get(roiFlag[pts[0].x][pts[0].y][1]);
						boolean okDistance = false;
						for (int u=0; u<r1.length; u++) {
							for (int v=0; v<r2.length; v++) {
								double currentDistance = java.lang.Math.sqrt(java.lang.Math.pow(r1[u].x-r2[v].x,2.)+java.lang.Math.pow(r1[u].y-r2[v].y,2.)); 
								if(currentDistance<(1.1)){
									okDistance = true;
								}
							}
						}
						if(!okDistance) {
							IJ.showMessage("Merging problem", "Only two touching objects can be merged together.");
						}
						else {
							// remove filled overlay for first object
							overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
							// remove the two objects to merge from objectsInEachClass and overlay, and then update
							removeRoi(firstObjectToMerge_class, firstObjectToMerge_classId, firstObjectToMerge_overlayId);
							int secondObjectToMerge_classId = roiFlag[pts[0].x][pts[0].y][1], secondObjectToMerge_overlayId = roiFlag[pts[0].x][pts[0].y][2];
							removeRoi(firstObjectToMerge_class, secondObjectToMerge_classId, secondObjectToMerge_overlayId);

							// create new roi with the 2 objects merged together
							int[] xPoints = new int[r1.length + r2.length];
							int[] yPoints = new int[r1.length + r2.length];
							int ptIndex = 0;
							for (int u=0; u<r1.length; u++) {
								/*PointRoi pt = new PointRoi(r1Pts[u].x,r1Pts[u].y);
							overlay.add(pt);*/
								xPoints[ptIndex] = r1[u].x;
								yPoints[ptIndex] = r1[u].y;
								ptIndex++;
							}
							for (int u=0; u<r2.length; u++) {
								/*PointRoi pt = new PointRoi(r2Pts[u].x,r2Pts[u].y);
							overlay.add(pt);*/
								xPoints[ptIndex] = r2[u].x;
								yPoints[ptIndex] = r2[u].y;
								ptIndex++;
							}
							// extract the added points that have less than 8 neighbors -> new roi contour
							/*boolean addedNucleus = drawNewObjectContour(xPoints,yPoints,firstObjectToMerge_class);
							if(addedNucleus) {
								for(int u = 0; u< xPoints.length; u++) {
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][0] = firstObjectToMerge_class;
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][1] = objectsInEachClass[firstObjectToMerge_class].size();
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][2] = overlay.size()-1;
								}
								FloatPolygon fPoly = new FloatPolygon(xPoints,yPoints);

								// save new nucleus as roi in the corresponding class
								objectsInEachClass[firstObjectToMerge_class].add(fPoly);
							}*/
							// extract non overlapping nucleus
							drawNewObjectContour(xPoints,yPoints,firstObjectToMerge_class);
							// add nucleus to the list of nuclei
							Point[] roiPoints = new Point[xPoints.length];
							for(int u = 0; u< xPoints.length; u++) {
								roiFlag[xPoints[u]][yPoints[u]][0] = firstObjectToMerge_class;
								roiFlag[xPoints[u]][yPoints[u]][1] = (short)objectsInEachClass[firstObjectToMerge_class].size();
								roiFlag[xPoints[u]][yPoints[u]][2] = (short)(overlay.size()-1);
								roiPoints[u] = new Point(xPoints[u],yPoints[u]);
							}
							// save new nucleus as roi in the corresponding class
							objectsInEachClass[firstObjectToMerge_class].add(roiPoints);

							firstObjectToMerge_class = -1;
							firstObjectToMerge_classId = -1;
							firstObjectToMerge_overlayId = -1;
						}
					}
				}
			}
		}
		//exampleList[i].add("trace " + traceCounter[i]); 
		//traceCounter[i]++;
		displayImage.updateAndDraw();
	}
	// neighbor extraction
	void neighbor2D(int x,int y,int[][] detect,int[][] flag,List<Point> cells, int width, int height){
		for(int v=-1;v<=1;v++){
			for(int u=-1;u<=1;u++){
				if(((x+u)>=0)&&((x+u)<width)&&((y+v)>=0)&&((y+v)<height)&&((Math.abs(u)+Math.abs(v))<2)){
					if((flag[x+u][y+v]==0)&&(detect[x+u][y+v]==1)){
						flag[x+u][y+v] = 1;
						Point pt = new Point(x+u,y+v);
						cells.add(pt);
						neighbor2D(x+u,y+v,detect,flag,cells,width,height);
					}
				}
			}
		}
	}

	/**
	 * Split objects
	 */
	private void splitObject()
	{
		//get selected region
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		// update flags for cell compartment computation
		nuclearComponentFlag = false;
		innerNuclearComponentFlag = false;
		membranarComponentFlag = false;
		cytoplasmicComponentFlag = false;
		rt_nuclearML_flag = false;
		
		/*ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int[] outputArray = new int[displayImage.getWidth()*displayImage.getHeight()];
		for(int y=0;y<displayImage.getHeight();y++) {
			for(int x=0;x<displayImage.getHeight();x++) {
				outputArray[y*displayImage.getWidth()+x] = roiFlag[x][y][2];
			}
		}
		stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), outputArray));
		ImagePlus test = new ImagePlus("test", stack);
		test.show();*/

		displayImage.killRoi();
		Point[] pts = r.getContainedPoints();
		if((roiFlag[pts[0].x][pts[0].y][2]!=(-1))||(roiFlag[pts[pts.length-1].x][pts[pts.length-1].y][2]!=(-1))) {
			IJ.showMessage("Split problem", "The line drawn to split a nucleus must split entirely one nucleus.");
		}
		else {
			short nucleusClass = -1, nucleusClassId = -1, nucleusOverlayId = -1;
			boolean uniqueNucleus=true;
			for(int u=0;u<pts.length;u++) {
				if(roiFlag[pts[u].x][pts[u].y][2]>(-1)) {
					if(nucleusOverlayId==(-1)) {
						nucleusClass = roiFlag[pts[u].x][pts[u].y][0];
						nucleusClassId = roiFlag[pts[u].x][pts[u].y][1];
						nucleusOverlayId = roiFlag[pts[u].x][pts[u].y][2];
					}
					else {
						if(roiFlag[pts[u].x][pts[u].y][2]!=nucleusOverlayId) {
							uniqueNucleus = false;
						}
					}
				}
			}
			if(!uniqueNucleus) {
				IJ.showMessage("Split problem", "The line drawn to split a nucleus must split only one nucleus.");
			}
			else {
				if(nucleusOverlayId==(-1)) {
					IJ.showMessage("Split problem", "The line drawn to split a nucleus must split at least one nucleus.");
				}
				else {
					// copy roi to split
					//Polygon rp = objectsInEachClass[nucleusClass].get(nucleusClassId).getPolygon();
					Point[] rp = objectsInEachClass[nucleusClass].get(nucleusClassId);

					// remove the object to split from objectsInEachClass and overlay, and then update
					removeRoi(nucleusClass, nucleusClassId, nucleusOverlayId);

					int[][] nucleusImage = new int[displayImage.getDimensions()[0]][displayImage.getDimensions()[1]], originalNucleusImage = new int[displayImage.getDimensions()[0]][displayImage.getDimensions()[1]], flag = new int[displayImage.getDimensions()[0]][displayImage.getDimensions()[1]];;
					for(int u=0;u<rp.length;u++) {
						nucleusImage[rp[u].x][rp[u].y] = 1;
						originalNucleusImage[rp[u].x][rp[u].y] = 1;
						flag[rp[u].x][rp[u].y] = 0;
					}

					for(int u=0;u<pts.length;u++) {
						if(originalNucleusImage[(int)pts[u].x][(int)pts[u].y]>0) {
							nucleusImage[(int)pts[u].x][(int)pts[u].y] = 0;
						}
					}

					boolean foundIndex=false;
					int startIndex=0;
					for(int u=0;u<rp.length;u++) {
						if(!foundIndex){
							if(nucleusImage[rp[u].x][rp[u].y]==1){
								startIndex=u;
								foundIndex = false;
							}
						}
					}
					List<Point> r1 = new ArrayList<Point>();
					neighbor2D(rp[startIndex].x, rp[startIndex].y, nucleusImage, flag, r1, displayImage.getDimensions()[0], displayImage.getDimensions()[1]);

					int[] xPoints1 = new int[r1.size()];
					int[] yPoints1 = new int[r1.size()];
					for(int u=0;u<r1.size();u++) {
						xPoints1[u] = r1.get(u).x;
						yPoints1[u] = r1.get(u).y;
					}

					// update display
					drawNewObjectContour(xPoints1,yPoints1,nucleusClass);
					// add nucleus to the list of nuclei
					Point[] roiPoints1 = new Point[xPoints1.length];
					for(int u = 0; u< xPoints1.length; u++) {
						roiFlag[xPoints1[u]][yPoints1[u]][0] = nucleusClass;
						roiFlag[xPoints1[u]][yPoints1[u]][1] = (short)objectsInEachClass[nucleusClass].size();
						roiFlag[xPoints1[u]][yPoints1[u]][2] = (short)(overlay.size()-1);
						roiPoints1[u] = new Point(xPoints1[u],yPoints1[u]);
					}
					// save new nucleus as roi in the corresponding class
					objectsInEachClass[nucleusClass].add(roiPoints1);

					// second object
					int firstPtInLineX = -1, firstPtInLineY = -1;
					for(int u=0;u<pts.length;u++) {
						if(originalNucleusImage[pts[u].x][pts[u].y]==1){
							nucleusImage[pts[u].x][pts[u].y] = 1;
							if(firstPtInLineX<0) {
								firstPtInLineX = pts[u].x;
								firstPtInLineY = pts[u].y;
							}
						}
					}

					List<Point> r2 = new ArrayList<Point>();
					neighbor2D(firstPtInLineX, firstPtInLineY, nucleusImage, flag, r2, displayImage.getDimensions()[0], displayImage.getDimensions()[1]);

					int[] xPoints2 = new int[r2.size()];
					int[] yPoints2 = new int[r2.size()];
					for(int u=0;u<r2.size();u++) {
						xPoints2[u] = r2.get(u).x;
						yPoints2[u] = r2.get(u).y;
					}

					// update display
					drawNewObjectContour(xPoints2,yPoints2,nucleusClass);
					// add nucleus to the list of nuclei
					Point[] roiPoints2 = new Point[xPoints2.length];
					for(int u = 0; u< xPoints2.length; u++) {
						roiFlag[xPoints2[u]][yPoints2[u]][0] = nucleusClass;
						roiFlag[xPoints2[u]][yPoints2[u]][1] = (short)objectsInEachClass[nucleusClass].size();
						roiFlag[xPoints2[u]][yPoints2[u]][2] = (short)(overlay.size()-1);
						roiPoints2[u] = new Point(xPoints2[u],yPoints2[u]);
					}
					// save new nucleus as roi in the corresponding class
					objectsInEachClass[nucleusClass].add(roiPoints2);
				}
			}
		}
	}
	/**
	 * Swap object class
	 */
	private void swapObjectClass()
	{
		//get selected region
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		// update flags for cell compartment computation
		nuclearComponentFlag = false;
		innerNuclearComponentFlag = false;
		membranarComponentFlag = false;
		cytoplasmicComponentFlag = false;
		rt_nuclearML_flag = false;
		
		displayImage.killRoi();

		Point[] pts = r.getContainedPoints();
		if(roiFlag[pts[0].x][pts[0].y][0]!=currentClass) {
			int objectCurrentClass = roiFlag[pts[0].x][pts[0].y][0], objectClassId = roiFlag[pts[0].x][pts[0].y][1], objectOverlayId = roiFlag[pts[0].x][pts[0].y][2];
			//Polygon fp = objectsInEachClass[objectCurrentClass].get(objectClassId).getPolygon();
			Point[] fp = objectsInEachClass[objectCurrentClass].get(objectClassId);
			// duplicate object coordinates
			int [] newRoiX = new int[fp.length], newRoiY = new int[fp.length];
			Point[] roiPoints = new Point[fp.length];
			for(int u = 0; u< fp.length; u++) {
				newRoiX[u] = fp[u].x;
				newRoiY[u] = fp[u].y;
				roiFlag[newRoiX[u]][newRoiY[u]][0] = currentClass;
				roiFlag[newRoiX[u]][newRoiY[u]][1] = (short)objectsInEachClass[currentClass].size();
				roiFlag[newRoiX[u]][newRoiY[u]][2] = (short)overlay.size();
				roiPoints[u] = new Point(newRoiX[u],newRoiY[u]);
			}
			removeRoi(objectCurrentClass, objectClassId, objectOverlayId);
			//PolygonRoi fPoly = new PolygonRoi(newRoiX,newRoiY,newRoiX.length,Roi.FREEROI);
			// save new nucleus as roi in the corresponding class
			objectsInEachClass[currentClass].add(roiPoints);
			drawNewObjectContour(newRoiX, newRoiY, currentClass);
		}
	}
	/**
	 * Swap area class
	 */
	private void swapAreaClass()
	{
		//get selected region
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		displayImage.killRoi();

		Point[] pts = r.getContainedPoints();
		if(areaFlag[pts[0].x][pts[0].y][0]!=currentArea) {
			int objectCurrentClass = areaFlag[pts[0].x][pts[0].y][0], objectClassId = areaFlag[pts[0].x][pts[0].y][1], objectOverlayId = areaFlag[pts[0].x][pts[0].y][2];
			Point[] fp = areasInEachClass[objectCurrentClass].get(objectClassId);
			removeAreaRoi(objectCurrentClass, objectClassId, objectOverlayId);
			// duplicate object coordinates
			int [] newRoiX = new int[fp.length], newRoiY = new int[fp.length];
			Point[] roiPoints = new Point[fp.length];
			for(int u = 0; u< fp.length; u++) {
				newRoiX[u] = fp[u].x;
				newRoiY[u] = fp[u].y;
				areaFlag[fp[u].x][fp[u].y][0] = currentArea;
				areaFlag[fp[u].x][fp[u].y][1] = (short)areasInEachClass[currentArea].size();
				areaFlag[fp[u].x][fp[u].y][2] = (short)overlay.size();
				roiPoints[u] = new Point(newRoiX[u],newRoiY[u]);
			}
			// save new nucleus as roi in the corresponding class
			areasInEachClass[currentArea].add(roiPoints);
			drawArea(roiPoints,currentArea);
		}
	}
	/**
	 * Remove objects
	 */
	private void removeArea()
	{
		//get selected region
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		displayImage.killRoi();

		Point[] pts = r.getContainedPoints();
		if(areaFlag[pts[0].x][pts[0].y][0]>(-1)) {
			int objectIdToRemove = areaFlag[pts[0].x][pts[0].y][1], areaClassToRemove = areaFlag[pts[0].x][pts[0].y][0], overlayIdToRemove = areaFlag[pts[0].x][pts[0].y][2];
			removeAreaRoi(areaClassToRemove, objectIdToRemove, overlayIdToRemove);			
		}
		displayImage.updateAndDraw();
	}

	/**
	 * Annotate nuclei markers
	 */
	void activateNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[objectAssociatedMarkersColors[currentObjectAssociatedMarker][currentPattern]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(2);
				positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].add(roiFlag[pt.x][pt.y][2]);
			}
		}
	}
	void deactivateNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				if(markersOverlay.get(roiFlag[pt.x][pt.y][2]).getStrokeColor()==(colors[objectAssociatedMarkersColors[currentObjectAssociatedMarker][currentPattern]])) {
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[classColors[roiFlag[pt.x][pt.y][0]]]);
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(0);
					for(int i = 0; i < positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].size(); i++) {
						if(positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].get(i)==roiFlag[pt.x][pt.y][2]) {
							positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].remove(i);
						}
					}
				}
				else {
					for(int k=0;k<4;k++) {
						if(k!= currentPattern) {
							for(int i = 0; i < positiveNucleiForEachMarker[currentObjectAssociatedMarker][k].size(); i++) {
								if(positiveNucleiForEachMarker[currentObjectAssociatedMarker][k].get(i)==roiFlag[pt.x][pt.y][2]) {
									positiveNucleiForEachMarker[currentObjectAssociatedMarker][k].remove(i);
								}
							}
							activateNucleusMarker(pt);
						}
					}
				}
			}
		}
	}
	private void annotateNucleusMarker()
	{
		if(currentObjectAssociatedMarker>(-1)) {
			//get selected region
			Roi r = displayImage.getRoi();
			if (null == r){
				return;
			}
			displayImage.killRoi();
			Point[] pts = r.getContainedPoints();
			if(roiFlag[pts[0].x][pts[0].y][0]>(-1)) {
				if(markersOverlay.get(roiFlag[pts[0].x][pts[0].y][2]).getStrokeWidth()>0){
					deactivateNucleusMarker(pts[0]);
				}
				else {
					activateNucleusMarker(pts[0]);
				}
			}
			displayImage.updateAndDraw();
		}
	}
	/**
	 * Label nuclei markers for ML
	 */
	void activatePositivelyLabelledNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[objectAssociatedMarkersMLColors[currentObjectAssociatedMarker][0]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(2);
				positivelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].add(roiFlag[pt.x][pt.y][2]);
			}
		}
	}
	void deactivatePositivelyLabelledNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[classColors[roiFlag[pt.x][pt.y][0]]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(0);
				for(int i = 0; i < positivelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].size(); i++) {
					if(positivelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].get(i)==roiFlag[pt.x][pt.y][2]) {
						positivelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].remove(i);
					}
				}
			}
		}
	}
	void activateNegativelyLabelledNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[objectAssociatedMarkersMLColors[currentObjectAssociatedMarker][1]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(2);
				negativelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].add(roiFlag[pt.x][pt.y][2]);
			}
		}
	}
	void deactivateNegativelyLabelledNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[classColors[roiFlag[pt.x][pt.y][0]]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(0);
				for(int i = 0; i < negativelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].size(); i++) {
					if(negativelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].get(i)==roiFlag[pt.x][pt.y][2]) {
						negativelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].remove(i);
					}
				}
			}
		}
	}
	void activateNucleusMarkerML(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[objectAssociatedMarkersMLColors[currentObjectAssociatedMarker][2]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(2);
				positiveNucleiForEachMarker[currentObjectAssociatedMarker][0].add(roiFlag[pt.x][pt.y][2]);
			}
		}
	}
	void deactivateNucleusMarkerML(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[classColors[roiFlag[pt.x][pt.y][0]]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(0);
				for(int i = 0; i < positiveNucleiForEachMarker[currentObjectAssociatedMarker][0].size(); i++) {
					if(positiveNucleiForEachMarker[currentObjectAssociatedMarker][0].get(i)==roiFlag[pt.x][pt.y][2]) {
						positiveNucleiForEachMarker[currentObjectAssociatedMarker][0].remove(i);
					}
				}
			}
		}
	}
	private void labelNucleusMarker()
	{
		if(currentObjectAssociatedMarker>(-1)) {
			//get selected region
			Roi r = displayImage.getRoi();
			if (null == r){
				return;
			}
			displayImage.killRoi();
			Point[] pts = r.getContainedPoints();
			if(roiFlag[pts[0].x][pts[0].y][0]>(-1)) {
				if(positiveLabelFlag){
					if(markersOverlay.get(roiFlag[pts[0].x][pts[0].y][2]).getStrokeWidth()==2){
						if(markersOverlay.get(roiFlag[pts[0].x][pts[0].y][2]).getStrokeColor()==colors[objectAssociatedMarkersMLColors[currentObjectAssociatedMarker][0]]){
							deactivatePositivelyLabelledNucleusMarker(pts[0]);
						}
						else if(markersOverlay.get(roiFlag[pts[0].x][pts[0].y][2]).getStrokeColor()==colors[objectAssociatedMarkersMLColors[currentObjectAssociatedMarker][1]]){
							deactivateNegativelyLabelledNucleusMarker(pts[0]);
							activatePositivelyLabelledNucleusMarker(pts[0]);
						}
						else{
							deactivateNucleusMarkerML(pts[0]);
							activatePositivelyLabelledNucleusMarker(pts[0]);
						}
					}
					else{
						activatePositivelyLabelledNucleusMarker(pts[0]);
					}
				}
				else{
					if(markersOverlay.get(roiFlag[pts[0].x][pts[0].y][2]).getStrokeWidth()==2){
						if(markersOverlay.get(roiFlag[pts[0].x][pts[0].y][2]).getStrokeColor()==colors[objectAssociatedMarkersMLColors[currentObjectAssociatedMarker][1]]){
							deactivateNegativelyLabelledNucleusMarker(pts[0]);
						}
						else if(markersOverlay.get(roiFlag[pts[0].x][pts[0].y][2]).getStrokeColor()==colors[objectAssociatedMarkersMLColors[currentObjectAssociatedMarker][0]]){
							deactivatePositivelyLabelledNucleusMarker(pts[0]);
							activateNegativelyLabelledNucleusMarker(pts[0]);
						}
						else{
							deactivateNucleusMarkerML(pts[0]);
							activateNegativelyLabelledNucleusMarker(pts[0]);
						}
					}
					else{
						activateNegativelyLabelledNucleusMarker(pts[0]);
					}
				}
			}
			displayImage.updateAndDraw();
		}
	}
	/**
	 * Annotate nuclei markers with thresholding
	 */
	void activateNucleusMarkerThresholding(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				if(markersOverlay.get(roiFlag[pt.x][pt.y][2]).getStrokeWidth()==0) {
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[objectAssociatedMarkersColors[currentObjectAssociatedMarker][currentPattern]]);
					//markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(2);
					positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].add(roiFlag[pt.x][pt.y][2]);
				}
			}
		}
	}
	void deactivateNucleusMarkerThresholding(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				if(markersOverlay.get(roiFlag[pt.x][pt.y][2]).getStrokeColor()==(colors[objectAssociatedMarkersColors[currentObjectAssociatedMarker][currentPattern]])) {
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(transparentColor);//colors[classColors[roiFlag[pt.x][pt.y][0]]]);
					//markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(0);
					for(int i = 0; i < positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].size(); i++) {
						if(positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].get(i)==roiFlag[pt.x][pt.y][2]) {
							positiveNucleiForEachMarker[currentObjectAssociatedMarker][currentPattern].remove(i);
						}
					}
				}
			}
		}
	}

	/**
	 * Update annotation buttons as only one annotation action can be done at once
	 */
	void updateRadioButtons(int pressedButton)
	{
		if(pressedButton==0) {
			if(mergeObjectsButton.isSelected()) {
				if(firstObjectToMerge_class>-1) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
					displayImage.updateAndDraw();
				}
			}
			newObjectButton.setSelected(true);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(false);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(false);
			newAreaButton.setSelected(false);
			removeAreaButton.setSelected(false);
			swapAreaClassButton.setSelected(false);
			Toolbar.getInstance().setTool(Toolbar.FREEROI);
		}
		else if(pressedButton==1) {
			if(mergeObjectsButton.isSelected()) {
				if(firstObjectToMerge_class>-1) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
					displayImage.updateAndDraw();
				}
			}
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(true);
			mergeObjectsButton.setSelected(false);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(false);
			newAreaButton.setSelected(false);
			removeAreaButton.setSelected(false);
			swapAreaClassButton.setSelected(false);
			Toolbar.getInstance().setTool(Toolbar.POINT);
		}
		else if(pressedButton==2) {
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(true);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(false);
			newAreaButton.setSelected(false);
			removeAreaButton.setSelected(false);
			swapAreaClassButton.setSelected(false);
			Toolbar.getInstance().setTool(Toolbar.POINT);
		}
		else if(pressedButton==3) {
			if(mergeObjectsButton.isSelected()) {
				if(firstObjectToMerge_class>-1) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
					displayImage.updateAndDraw();
				}
			}
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(false);
			splitObjectsButton.setSelected(true);
			swapObjectClassButton.setSelected(false);
			newAreaButton.setSelected(false);
			removeAreaButton.setSelected(false);
			swapAreaClassButton.setSelected(false);
			Toolbar.getInstance().setTool(Toolbar.FREELINE);
		}
		else if(pressedButton==4) {
			if(mergeObjectsButton.isSelected()) {
				if(firstObjectToMerge_class>-1) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
					displayImage.updateAndDraw();
				}
			}
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(false);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(true);
			newAreaButton.setSelected(false);
			removeAreaButton.setSelected(false);
			swapAreaClassButton.setSelected(false);
			Toolbar.getInstance().setTool(Toolbar.POINT);
		}
		else if(pressedButton==5) {
			if(mergeObjectsButton.isSelected()) {
				if(firstObjectToMerge_class>-1) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
					displayImage.updateAndDraw();
				}
			}
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(false);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(false);
			newAreaButton.setSelected(true);
			removeAreaButton.setSelected(false);
			swapAreaClassButton.setSelected(false);
			Toolbar.getInstance().setTool(Toolbar.FREEROI);
		}
		else if(pressedButton==6) {
			if(mergeObjectsButton.isSelected()) {
				if(firstObjectToMerge_class>-1) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
					displayImage.updateAndDraw();
				}
			}
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(false);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(false);
			newAreaButton.setSelected(false);
			removeAreaButton.setSelected(true);
			swapAreaClassButton.setSelected(false);
			Toolbar.getInstance().setTool(Toolbar.POINT);
		}
		else if(pressedButton==7) {
			if(mergeObjectsButton.isSelected()) {
				if(firstObjectToMerge_class>-1) {
					overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
					firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
					displayImage.updateAndDraw();
				}
			}
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(false);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(false);
			newAreaButton.setSelected(false);
			removeAreaButton.setSelected(false);
			swapAreaClassButton.setSelected(true);
			Toolbar.getInstance().setTool(Toolbar.POINT);
		}
	}

	/**
	 * Update annotation buttons as only one annotation action can be done at once
	 */
	void updateModeRadioButtons(int pressedButton)
	{
		if(pressedButton==0) {
			initializeVisualizeChannelButtons1();
			visualizeAllChannelsButton1.setSelected(true);
			if(objectDisplayFlag){visualizeObjectsButton1.setSelected(true);}
			else{visualizeObjectsButton1.setSelected(false);}
			if(areaDisplayFlag){visualizeAreasButton1.setSelected(true);}
			else{visualizeAreasButton1.setSelected(false);}

			displayFlag = 0;

			objectsAnnotationButton.setSelected(true);
			markerAnnotationButton.setSelected(false);
			currentMode = 0;
			removeMarkersFromOverlay();
			currentObjectAssociatedMarker = -1;
		}
		else if(pressedButton==1) {
			initializeVisualizeChannelButtons2();
			visualizeAllChannelsButton2.setSelected(true);
			if(objectDisplayFlag){visualizeObjectsButton2.setSelected(true);}
			else{visualizeObjectsButton2.setSelected(false);}
			if(areaDisplayFlag){visualizeAreasButton2.setSelected(true);}
			else{visualizeAreasButton2.setSelected(false);}
			displayFlag = 0;
			
			objectsAnnotationButton.setSelected(false);
			markerAnnotationButton.setSelected(true);
			currentMode = 1;
			displayFlag = 0;
			if(firstObjectToMerge_class>-1) {
				overlay.get(firstObjectToMerge_overlayId).setStrokeWidth(0);
				firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
			}
		}

		displayImage.setDisplayMode(IJ.COMPOSITE);
		displayImage.setPosition(currentDisplayedChannel+1, displayImage.getSlice(), displayImage.getFrame());
		currentDisplayedChannel = -1;

		//Build GUI
		//win = new CustomWindow(displayImage);
		//win.pack();
		repaintWindow();

	}

	/**
	 * Update annotation buttons as only one annotation action can be done at once
	 */
	void updateClassesButtons(int pressedButton)
	{
		if(pressedButton==0) {
			class1Button.setSelected(true);
			class2Button.setSelected(false);
			class3Button.setSelected(false);
			class4Button.setSelected(false);
			class5Button.setSelected(false);
			currentClass = 0;
			updateRadioButtons(0);
		}
		else if(pressedButton==1) {
			class1Button.setSelected(false);
			class2Button.setSelected(true);
			class3Button.setSelected(false);
			class4Button.setSelected(false);
			class5Button.setSelected(false);
			currentClass = 1;
			updateRadioButtons(0);
		}
		else if(pressedButton==2) {
			class1Button.setSelected(false);
			class2Button.setSelected(false);
			class3Button.setSelected(true);
			class4Button.setSelected(false);
			class5Button.setSelected(false);
			currentClass = 2;
			updateRadioButtons(0);
		}
		else if(pressedButton==3) {
			class1Button.setSelected(false);
			class2Button.setSelected(false);
			class3Button.setSelected(false);
			class4Button.setSelected(true);
			class5Button.setSelected(false);
			currentClass = 3;
			updateRadioButtons(0);
		}
		else if(pressedButton==4) {
			class1Button.setSelected(false);
			class2Button.setSelected(false);
			class3Button.setSelected(false);
			class4Button.setSelected(false);
			class5Button.setSelected(true);
			currentClass = 4;
			updateRadioButtons(0);
		}
	}
	/**
	 * Update annotation buttons as only one annotation action can be done at once
	 */
	void updateAreaButtons(int pressedButton)
	{
		if(pressedButton==0) {
			area1Button.setSelected(true);
			area2Button.setSelected(false);
			area3Button.setSelected(false);
			area4Button.setSelected(false);
			area5Button.setSelected(false);
			currentArea = 0;
			updateRadioButtons(5);
		}
		else if(pressedButton==1) {
			area1Button.setSelected(false);
			area2Button.setSelected(true);
			area3Button.setSelected(false);
			area4Button.setSelected(false);
			area5Button.setSelected(false);
			currentArea = 1;
			updateRadioButtons(5);
		}
		else if(pressedButton==2) {
			area1Button.setSelected(false);
			area2Button.setSelected(false);
			area3Button.setSelected(true);
			area4Button.setSelected(false);
			area5Button.setSelected(false);
			currentArea = 2;
			updateRadioButtons(5);
		}
		else if(pressedButton==3) {
			area1Button.setSelected(false);
			area2Button.setSelected(false);
			area3Button.setSelected(false);
			area4Button.setSelected(true);
			area5Button.setSelected(false);
			currentArea = 3;
			updateRadioButtons(5);
		}
		else if(pressedButton==4) {
			area1Button.setSelected(false);
			area2Button.setSelected(false);
			area3Button.setSelected(false);
			area4Button.setSelected(false);
			area5Button.setSelected(true);
			currentArea = 4;
			updateRadioButtons(5);
		}
	}

	/**
	 * Update visualization
	 */
	void initializeVisualizeChannelButtons1() {
		visualizeChannel1Button1.setSelected(false);
		visualizeChannel2Button1.setSelected(false);
		visualizeChannel3Button1.setSelected(false);
		visualizeChannel4Button1.setSelected(false);
		visualizeChannel5Button1.setSelected(false);
		visualizeChannel6Button1.setSelected(false);
		visualizeChannel7Button1.setSelected(false);
		visualizeChannel1onlyButton1.setSelected(false);
		visualizeChannel2onlyButton1.setSelected(false);
		visualizeChannel3onlyButton1.setSelected(false);
		visualizeChannel4onlyButton1.setSelected(false);
		visualizeChannel5onlyButton1.setSelected(false);
		visualizeChannel6onlyButton1.setSelected(false);
		visualizeChannel7onlyButton1.setSelected(false);
		visualizeAllChannelsButton1.setSelected(false);
		
	}
	void initializeVisualizeChannelButtons1compositeMode() {
		visualizeChannel1onlyButton1.setSelected(false);
		visualizeChannel2onlyButton1.setSelected(false);
		visualizeChannel3onlyButton1.setSelected(false);
		visualizeChannel4onlyButton1.setSelected(false);
		visualizeChannel5onlyButton1.setSelected(false);
		visualizeChannel6onlyButton1.setSelected(false);
		visualizeChannel7onlyButton1.setSelected(false);
		visualizeAllChannelsButton1.setSelected(false);
	}
	String getChannelsForCompositeImage1() {
		String chs = "1";
		if(numOfChannels==1) {
			chs = Integer.toString(visualizeChannel1Button1.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==2) {
			chs = Integer.toString(visualizeChannel1Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button1.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==3) {
			chs = Integer.toString(visualizeChannel1Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button1.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==4) {
			chs = Integer.toString(visualizeChannel1Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button1.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==5) {
			chs = Integer.toString(visualizeChannel1Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel5Button1.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==6) {
			chs = Integer.toString(visualizeChannel1Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel5Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel6Button1.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==7) {
			chs = Integer.toString(visualizeChannel1Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel5Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel6Button1.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel7Button1.isSelected() ? 1 : 0);
		}
		return chs;
	}
	void updateVisualizeChannelButtons1(byte pressedButton)
	{
		if(pressedButton<10) {
			if(displayFlag==0) {
				displayImage.setDisplayMode(IJ.COMPOSITE);
				initializeVisualizeChannelButtons1compositeMode();
				displayFlag = 1;
			}
			String chs = getChannelsForCompositeImage1();
			displayImage.setActiveChannels(chs);
		}
		if(pressedButton==10) {
			initializeVisualizeChannelButtons1();
			visualizeChannel1onlyButton1.setSelected(true);
		}
		else if(pressedButton==11) {
			initializeVisualizeChannelButtons1();
			visualizeChannel2onlyButton1.setSelected(true);
		}
		else if(pressedButton==12) {
			initializeVisualizeChannelButtons1();
			visualizeChannel3onlyButton1.setSelected(true);
		}
		else if(pressedButton==13) {
			initializeVisualizeChannelButtons1();
			visualizeChannel4onlyButton1.setSelected(true);
		}
		else if(pressedButton==14) {
			initializeVisualizeChannelButtons1();
			visualizeChannel5onlyButton1.setSelected(true);
		}
		else if(pressedButton==15) {
			initializeVisualizeChannelButtons1();
			visualizeChannel6onlyButton1.setSelected(true);
		}
		else if(pressedButton==16) {
			initializeVisualizeChannelButtons1();
			visualizeChannel7onlyButton1.setSelected(true);
		}
		else if(pressedButton==20) {
			initializeVisualizeChannelButtons1();
			visualizeAllChannelsButton1.setSelected(true);
			displayFlag = 0;
			displayImage.setDisplayMode(IJ.COMPOSITE);
			displayImage.setPosition(currentDisplayedChannel+1, displayImage.getSlice(), displayImage.getFrame());
			//displayImage.setDisplayRange(originalLUT[currentDisplayedChannel].min, originalLUT[currentDisplayedChannel].max);
			displayImage.updateAndDraw();
			currentDisplayedChannel = -1;
		}
		if((pressedButton>9)&&(pressedButton<20)) {
			displayFlag = 0;
			displayImage.setDisplayMode(IJ.GRAYSCALE);
			/*if(currentDisplayedChannel>(-1)) {
				displayImage.setPosition(currentDisplayedChannel+1, displayImage.getSlice(), displayImage.getFrame());
				displayImage.setDisplayRange(originalLUT[currentDisplayedChannel].min, originalLUT[currentDisplayedChannel].max);
			}*/
			displayImage.setPosition(pressedButton-9, displayImage.getSlice(), displayImage.getFrame());
			//IJ.run("Enhance Contrast", "saturated=0.35");
			displayImage.updateAndDraw();
			currentDisplayedChannel = pressedButton;
		}
	}

	void initializeVisualizeChannelButtons2() {
		visualizeChannel1Button2.setSelected(false);
		visualizeChannel2Button2.setSelected(false);
		visualizeChannel3Button2.setSelected(false);
		visualizeChannel4Button2.setSelected(false);
		visualizeChannel5Button2.setSelected(false);
		visualizeChannel6Button2.setSelected(false);
		visualizeChannel7Button2.setSelected(false);
		visualizeChannel1onlyButton2.setSelected(false);
		visualizeChannel2onlyButton2.setSelected(false);
		visualizeChannel3onlyButton2.setSelected(false);
		visualizeChannel4onlyButton2.setSelected(false);
		visualizeChannel5onlyButton2.setSelected(false);
		visualizeChannel6onlyButton2.setSelected(false);
		visualizeChannel7onlyButton2.setSelected(false);
		visualizeAllChannelsButton2.setSelected(false);
	}
	void initializeVisualizeChannelButtons2compositeMode() {
		visualizeChannel1onlyButton2.setSelected(false);
		visualizeChannel2onlyButton2.setSelected(false);
		visualizeChannel3onlyButton2.setSelected(false);
		visualizeChannel4onlyButton2.setSelected(false);
		visualizeChannel5onlyButton2.setSelected(false);
		visualizeChannel6onlyButton2.setSelected(false);
		visualizeChannel7onlyButton2.setSelected(false);
		visualizeAllChannelsButton2.setSelected(false);
	}
	String getChannelsForCompositeImage2() {
		String chs = "1";
		if(numOfChannels==1) {
			chs = Integer.toString(visualizeChannel1Button2.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==2) {
			chs = Integer.toString(visualizeChannel1Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button2.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==3) {
			chs = Integer.toString(visualizeChannel1Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button2.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==4) {
			chs = Integer.toString(visualizeChannel1Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button2.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==5) {
			chs = Integer.toString(visualizeChannel1Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel5Button2.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==6) {
			chs = Integer.toString(visualizeChannel1Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel5Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel6Button2.isSelected() ? 1 : 0);
		}
		else if(numOfChannels==7) {
			chs = Integer.toString(visualizeChannel1Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel2Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel3Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel4Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel5Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel6Button2.isSelected() ? 1 : 0) + Integer.toString(visualizeChannel7Button2.isSelected() ? 1 : 0);
		}
		return chs;
	}
	void updateVisualizeChannelButtons2(byte pressedButton)
	{
		if(pressedButton<10) {
			if(displayFlag==0) {
				displayImage.setDisplayMode(IJ.COMPOSITE);
				initializeVisualizeChannelButtons2compositeMode();
				displayFlag = 1;
			}
			String chs = getChannelsForCompositeImage2();
			displayImage.setActiveChannels(chs);
		}
		if(pressedButton==10) {
			initializeVisualizeChannelButtons2();
			visualizeChannel1onlyButton2.setSelected(true);
		}
		else if(pressedButton==11) {
			initializeVisualizeChannelButtons2();
			visualizeChannel2onlyButton2.setSelected(true);
		}
		else if(pressedButton==12) {
			initializeVisualizeChannelButtons2();
			visualizeChannel3onlyButton2.setSelected(true);
		}
		else if(pressedButton==13) {
			initializeVisualizeChannelButtons2();
			visualizeChannel4onlyButton2.setSelected(true);
		}
		else if(pressedButton==14) {
			initializeVisualizeChannelButtons2();
			visualizeChannel5onlyButton2.setSelected(true);
		}
		else if(pressedButton==15) {
			initializeVisualizeChannelButtons2();
			visualizeChannel6onlyButton2.setSelected(true);
		}
		else if(pressedButton==16) {
			initializeVisualizeChannelButtons2();
			visualizeChannel7onlyButton2.setSelected(true);
		}
		else if(pressedButton==20) {
			initializeVisualizeChannelButtons2();
			visualizeAllChannelsButton2.setSelected(true);
			displayFlag = 0;
			displayImage.setDisplayMode(IJ.COMPOSITE);
			displayImage.setPosition(currentDisplayedChannel+1, displayImage.getSlice(), displayImage.getFrame());
			displayImage.updateAndDraw();
			currentDisplayedChannel = -1;
		}
		if((pressedButton>9)&&(pressedButton<20)) {
			displayFlag = 0;
			displayImage.setDisplayMode(IJ.GRAYSCALE);
			displayImage.setPosition(pressedButton-9, displayImage.getSlice(), displayImage.getFrame());
			displayImage.updateAndDraw();
			currentDisplayedChannel = pressedButton;
		}
	}
	/** add/remove objects/areas from overlays */
	void addObjectsToOverlay(){
		objectDisplayFlag = true;
		for(int c=0;c<numOfClasses;c++) {
			for(int i=0;i<objectsInEachClass[c].size();i++) {
				Point[] pts = objectsInEachClass[c].get(i);
				int currentX=-1,currentY=-1;
				if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
					currentX = pts[pts.length/2].x;
					currentY = pts[pts.length/2].y;
				}
				else {
					for(int k = 0; k < pts.length; k++) {
						if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
							currentX = pts[k].x;
							currentY = pts[k].y;
						}
					}
				}
				if(currentX>(-1)) {
					if(roiFlag[currentX][currentY][2]>(-1)) {
						if(roiFlag[currentX][pts[pts.length/2].y][2]>(-1)) {
							overlay.get(roiFlag[currentX][currentY][2]).setStrokeColor(colors[classColors[c]]);
							markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeColor(colors[classColors[c]]);
						}
					}
				}
			}
		}
		displayImage.updateAndDraw();
	}
	void removeObjectsFromOverlay(){
		objectDisplayFlag = false;
		if(currentMode==1){
			removeMarkersFromOverlay();
			initializeMarkerButtons();
			currentObjectAssociatedMarker = -1;
		}
		
		for(int c=0;c<numOfClasses;c++) {
			for(int i=0;i<objectsInEachClass[c].size();i++) {
				Point[] pts = objectsInEachClass[c].get(i);
				int currentX=-1,currentY=-1;
				if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
					currentX = pts[pts.length/2].x;
					currentY = pts[pts.length/2].y;
				}
				else {
					for(int k = 0; k < pts.length; k++) {
						if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
							currentX = pts[k].x;
							currentY = pts[k].y;
						}
					}
				}
				if(currentX>(-1)) {
					if(roiFlag[currentX][currentY][2]>(-1)) {
						if(roiFlag[currentX][pts[pts.length/2].y][2]>(-1)) {
							overlay.get(roiFlag[currentX][currentY][2]).setStrokeColor(transparentColor);
							markersOverlay.get(roiFlag[currentX][currentY][2]).setStrokeColor(transparentColor);
						}
					}
				}
			}
		}
		displayImage.updateAndDraw();
	}
	void addAreasFromScratchToOverlayVisible(){
		areaDisplayFlag = true;
		for(int c=0;c<numOfAreas;c++) {
			for(int i=0;i<areasInEachClass[c].size();i++) {
				Point[] pts = areasInEachClass[c].get(i);
				int[][] area = new int[displayImage.getWidth()][displayImage.getHeight()];
				for(int p=0;p<pts.length;p++){
					area[pts[p].x][pts[p].y] = 255;
				}
				ImageProcessor areaIP = new FloatProcessor(area);
				areaIP.setColorModel(areaColorModels[areaColors[c]]);
				ImageRoi roi = new ImageRoi(0, 0, areaIP);
				roi.setOpacity(0.2);
				roi.setZeroTransparent(true);
				overlay.add(roi);
				markersOverlay.add(roi);
			}
		}
		displayImage.updateAndDraw();
	}
	void addAreasFromScratchToOverlayNonVisible(){
		areaDisplayFlag = true;
		for(int c=0;c<numOfAreas;c++) {
			for(int i=0;i<areasInEachClass[c].size();i++) {
				Point[] pts = areasInEachClass[c].get(i);
				int[][] area = new int[displayImage.getWidth()][displayImage.getHeight()];
				for(int p=0;p<pts.length;p++){
					area[pts[p].x][pts[p].y] = 255;
				}
				ImageProcessor areaIP = new FloatProcessor(area);
				areaIP.setColorModel(areaColorModels[areaColors[c]]);
				ImageRoi roi = new ImageRoi(0, 0, areaIP);
				roi.setOpacity(0.);
				roi.setZeroTransparent(true);
				overlay.add(roi);
				markersOverlay.add(roi);
			}
		}
		displayImage.updateAndDraw();
	}
	void addAreasToOverlay(){
		areaDisplayFlag = true;
		for(int c=0;c<numOfAreas;c++) {
			for(int i=0;i<areasInEachClass[c].size();i++) {
				Point[] pts = areasInEachClass[c].get(i);
				int[][] area = new int[displayImage.getWidth()][displayImage.getHeight()];
				int roiId = 0;
				for(int p=0;p<pts.length;p++){
					area[pts[p].x][pts[p].y] = 255;
					if(areaFlag[pts[p].x][pts[p].y][2]>(-1)){roiId = areaFlag[pts[p].x][pts[p].y][2];}
				}
				ImageProcessor areaIP = new FloatProcessor(area);
				areaIP.setColorModel(areaColorModels[areaColors[c]]);
				ImageRoi roi = new ImageRoi(0, 0, areaIP);
				roi.setOpacity(0.2);
				roi.setZeroTransparent(true);
				if(roiId>(-1)){
					overlay.set(roi,roiId);
					markersOverlay.set(roi,roiId);
				}
			}
		}
		displayImage.updateAndDraw();
	}
	void removeAreasFromOverlay(){
		areaDisplayFlag = false;
		for(int c=0;c<numOfAreas;c++) {
			for(int i=0;i<areasInEachClass[c].size();i++) {
				Point[] pts = areasInEachClass[c].get(i);
				int[][] area = new int[displayImage.getWidth()][displayImage.getHeight()];
				int roiId = 0;
				for(int p=0;p<pts.length;p++){
					area[pts[p].x][pts[p].y] = 255;
					if(areaFlag[pts[p].x][pts[p].y][2]>(-1)){roiId = areaFlag[pts[p].x][pts[p].y][2];}
				}
				ImageProcessor areaIP = new FloatProcessor(area);
				areaIP.setColorModel(areaColorModels[areaColors[c]]);
				ImageRoi roi = new ImageRoi(0, 0, areaIP);
				roi.setOpacity(0.);
				roi.setZeroTransparent(true);
				if(roiId>(-1)){
					overlay.set(roi,roiId);
					markersOverlay.set(roi,roiId);
				}
			}
		}
		displayImage.updateAndDraw();
	}
	/**
	 * Update analyze channels buttons as only one channel can be annotated at once
	 */
	void initializeMarkerButtons() {
		objectAssociatedMarker1Button.setSelected(false);
		objectAssociatedMarker1PositiveLabelButton.setSelected(false);
		objectAssociatedMarker1NegativeLabelButton.setSelected(false);
		objectAssociatedMarker1Pattern1Button.setSelected(false);
		objectAssociatedMarker1Pattern2Button.setSelected(false);
		objectAssociatedMarker1Pattern3Button.setSelected(false);
		objectAssociatedMarker1Pattern4Button.setSelected(false);
		objectAssociatedMarker2Button.setSelected(false);
		objectAssociatedMarker2PositiveLabelButton.setSelected(false);
		objectAssociatedMarker2NegativeLabelButton.setSelected(false);
		objectAssociatedMarker2Pattern1Button.setSelected(false);
		objectAssociatedMarker2Pattern2Button.setSelected(false);
		objectAssociatedMarker2Pattern3Button.setSelected(false);
		objectAssociatedMarker2Pattern4Button.setSelected(false);
		objectAssociatedMarker3Button.setSelected(false);
		objectAssociatedMarker3PositiveLabelButton.setSelected(false);
		objectAssociatedMarker3NegativeLabelButton.setSelected(false);
		objectAssociatedMarker3Pattern1Button.setSelected(false);
		objectAssociatedMarker3Pattern2Button.setSelected(false);
		objectAssociatedMarker3Pattern3Button.setSelected(false);
		objectAssociatedMarker3Pattern4Button.setSelected(false);
		objectAssociatedMarker4Button.setSelected(false);
		objectAssociatedMarker4PositiveLabelButton.setSelected(false);
		objectAssociatedMarker4NegativeLabelButton.setSelected(false);
		objectAssociatedMarker4Pattern1Button.setSelected(false);
		objectAssociatedMarker4Pattern2Button.setSelected(false);
		objectAssociatedMarker4Pattern3Button.setSelected(false);
		objectAssociatedMarker4Pattern4Button.setSelected(false);
		objectAssociatedMarker5Button.setSelected(false);
		objectAssociatedMarker5PositiveLabelButton.setSelected(false);
		objectAssociatedMarker5NegativeLabelButton.setSelected(false);
		objectAssociatedMarker5Pattern1Button.setSelected(false);
		objectAssociatedMarker5Pattern2Button.setSelected(false);
		objectAssociatedMarker5Pattern3Button.setSelected(false);
		objectAssociatedMarker5Pattern4Button.setSelected(false);
		objectAssociatedMarker6Button.setSelected(false);
		objectAssociatedMarker6PositiveLabelButton.setSelected(false);
		objectAssociatedMarker6NegativeLabelButton.setSelected(false);
		objectAssociatedMarker6Pattern1Button.setSelected(false);
		objectAssociatedMarker6Pattern2Button.setSelected(false);
		objectAssociatedMarker6Pattern3Button.setSelected(false);
		objectAssociatedMarker6Pattern4Button.setSelected(false);
		objectAssociatedMarker7Button.setSelected(false);
		objectAssociatedMarker7PositiveLabelButton.setSelected(false);
		objectAssociatedMarker7NegativeLabelButton.setSelected(false);
		objectAssociatedMarker7Pattern1Button.setSelected(false);
		objectAssociatedMarker7Pattern2Button.setSelected(false);
		objectAssociatedMarker7Pattern3Button.setSelected(false);
		objectAssociatedMarker7Pattern4Button.setSelected(false);
	}
	void activateCurrentNucleiMarkerOverlays(int marker) {
		for(int i = 0; i < positiveNucleiForEachMarker[marker][0].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][0].get(i)).setStrokeColor(colors[objectAssociatedMarkersColors[marker][0]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][0].get(i)).setStrokeWidth(2);
		}
		for(int i = 0; i < positiveNucleiForEachMarker[marker][1].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][1].get(i)).setStrokeColor(colors[objectAssociatedMarkersColors[marker][1]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][1].get(i)).setStrokeWidth(2);
		}
		for(int i = 0; i < positiveNucleiForEachMarker[marker][2].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][2].get(i)).setStrokeColor(colors[objectAssociatedMarkersColors[marker][2]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][2].get(i)).setStrokeWidth(2);
		}
		for(int i = 0; i < positiveNucleiForEachMarker[marker][3].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][3].get(i)).setStrokeColor(colors[objectAssociatedMarkersColors[marker][3]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][3].get(i)).setStrokeWidth(2);
		}
		if(methodToIdentifyObjectAssociatedMarkers[marker]==2){
			// activate ML labelled
			for(int i = 0; i < positivelyLabelledNucleiForEachMarker[marker].size(); i++) {
				markersOverlay.get(positivelyLabelledNucleiForEachMarker[marker].get(i)).setStrokeColor(colors[objectAssociatedMarkersMLColors[marker][0]]);
				markersOverlay.get(positivelyLabelledNucleiForEachMarker[marker].get(i)).setStrokeWidth(2);
			}
			for(int i = 0; i < negativelyLabelledNucleiForEachMarker[marker].size(); i++) {
				markersOverlay.get(negativelyLabelledNucleiForEachMarker[marker].get(i)).setStrokeColor(colors[objectAssociatedMarkersMLColors[marker][1]]);
				markersOverlay.get(negativelyLabelledNucleiForEachMarker[marker].get(i)).setStrokeWidth(2);
			}
		}
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
	}
	void updateAnnotateObjectAssociatedMarker(int pressedButton, boolean exception)
	{
		if(!exception){
			if(!objectDisplayFlag){addObjectsToOverlay();visualizeObjectsButton2.setSelected(true);}
		}
		if(pressedButton==0) {
			initializeMarkerButtons();
			objectAssociatedMarker1Button.setSelected(true);
			if(methodToIdentifyObjectAssociatedMarkers[0]<2){
				objectAssociatedMarker1Pattern1Button.setSelected(true);
			}
			else{
				positiveLabelFlag = true;
				objectAssociatedMarker1PositiveLabelButton.setSelected(true);
			}
			if(currentObjectAssociatedMarker!=0) {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(0);
			}
		}
		else if(pressedButton==1) {
			initializeMarkerButtons();
			objectAssociatedMarker2Button.setSelected(true);
			if(methodToIdentifyObjectAssociatedMarkers[1]<2){
				objectAssociatedMarker2Pattern1Button.setSelected(true);
			}
			else{
				positiveLabelFlag = true;
				objectAssociatedMarker2PositiveLabelButton.setSelected(true);
			}
			if(currentObjectAssociatedMarker!=1) {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(1);
			}
		}
		else if(pressedButton==2) {
			initializeMarkerButtons();
			objectAssociatedMarker3Button.setSelected(true);
			if(methodToIdentifyObjectAssociatedMarkers[2]<2){
				objectAssociatedMarker3Pattern1Button.setSelected(true);
			}
			else{
				positiveLabelFlag = true;
				objectAssociatedMarker3PositiveLabelButton.setSelected(true);
			}
			if(currentObjectAssociatedMarker!=2) {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(2);
			}
		}
		else if(pressedButton==3) {
			initializeMarkerButtons();
			objectAssociatedMarker4Button.setSelected(true);
			if(methodToIdentifyObjectAssociatedMarkers[3]<2){
				objectAssociatedMarker4Pattern1Button.setSelected(true);
			}
			else{
				positiveLabelFlag = true;
				objectAssociatedMarker4PositiveLabelButton.setSelected(true);
			}
			if(currentObjectAssociatedMarker!=3) {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(3);
			}
		}
		else if(pressedButton==4) {
			initializeMarkerButtons();
			objectAssociatedMarker5Button.setSelected(true);
			if(methodToIdentifyObjectAssociatedMarkers[4]<2){
				objectAssociatedMarker5Pattern1Button.setSelected(true);
			}
			else{
				positiveLabelFlag = true;
				objectAssociatedMarker5PositiveLabelButton.setSelected(true);
			}
			if(currentObjectAssociatedMarker!=4) {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(4);
			}
		}
		else if(pressedButton==5) {
			initializeMarkerButtons();
			objectAssociatedMarker6Button.setSelected(true);
			if(methodToIdentifyObjectAssociatedMarkers[5]<2){
				objectAssociatedMarker6Pattern1Button.setSelected(true);
			}
			else{
				positiveLabelFlag = true;
				objectAssociatedMarker6PositiveLabelButton.setSelected(true);
			}
			if(currentObjectAssociatedMarker!=5) {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(5);
			}
		}
		else if(pressedButton==6) {
			initializeMarkerButtons();
			objectAssociatedMarker7Button.setSelected(true);
			if(methodToIdentifyObjectAssociatedMarkers[6]<2){
				objectAssociatedMarker7Pattern1Button.setSelected(true);
			}
			else{
				positiveLabelFlag = true;
				objectAssociatedMarker7PositiveLabelButton.setSelected(true);
			}
			if(currentObjectAssociatedMarker!=6) {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(6);
			}
		}
		displayImage.updateAndDraw();
		/*if(visualizeAllChannelsButton2.isSelected()) {
			visualizeAllChannelsButton2.setSelected(false);
		}
		displayImage.setDisplayMode(IJ.GRAYSCALE);
		displayImage.setPosition(currentChannel+1, displayImage.getSlice(), displayImage.getFrame());
		IJ.run("Enhance Contrast", "saturated=0.35");
		displayImage.updateAndDraw();*/
	}
	/**
	 * Update visualization pattern for mode nuclei marker annotation
	 */
	void updateAnnotateChannelPatternButtons(int pressedButton)
	{
		if(currentObjectAssociatedMarker>(-1)) {
			if(((currentObjectAssociatedMarker*6)<=pressedButton)&&(((currentObjectAssociatedMarker+1)*6)>pressedButton)) {
				if(pressedButton==0) {
					initializeMarkerButtons();
					objectAssociatedMarker1Button.setSelected(true);
					objectAssociatedMarker1Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==1) {
					initializeMarkerButtons();
					objectAssociatedMarker1Button.setSelected(true);
					objectAssociatedMarker1Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==2) {
					initializeMarkerButtons();
					objectAssociatedMarker1Button.setSelected(true);
					objectAssociatedMarker1Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==3) {
					initializeMarkerButtons();
					objectAssociatedMarker1Button.setSelected(true);
					objectAssociatedMarker1Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==4) {
					positiveLabelFlag = true;
					initializeMarkerButtons();
					objectAssociatedMarker1Button.setSelected(true);
					objectAssociatedMarker1PositiveLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==5) {
					positiveLabelFlag = false;
					initializeMarkerButtons();
					objectAssociatedMarker1Button.setSelected(true);
					objectAssociatedMarker1NegativeLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==6) {
					initializeMarkerButtons();
					objectAssociatedMarker2Button.setSelected(true);
					objectAssociatedMarker2Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==7) {
					initializeMarkerButtons();
					objectAssociatedMarker2Button.setSelected(true);
					objectAssociatedMarker2Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==8) {
					initializeMarkerButtons();
					objectAssociatedMarker2Button.setSelected(true);
					objectAssociatedMarker2Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==9) {
					initializeMarkerButtons();
					objectAssociatedMarker2Button.setSelected(true);
					objectAssociatedMarker2Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==10) {
					positiveLabelFlag = true;
					initializeMarkerButtons();
					objectAssociatedMarker2Button.setSelected(true);
					objectAssociatedMarker2PositiveLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==11) {
					positiveLabelFlag = false;
					initializeMarkerButtons();
					objectAssociatedMarker2Button.setSelected(true);
					objectAssociatedMarker2NegativeLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==12) {
					initializeMarkerButtons();
					objectAssociatedMarker3Button.setSelected(true);
					objectAssociatedMarker3Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==13) {
					initializeMarkerButtons();
					objectAssociatedMarker3Button.setSelected(true);
					objectAssociatedMarker3Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==14) {
					initializeMarkerButtons();
					objectAssociatedMarker3Button.setSelected(true);
					objectAssociatedMarker3Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==15) {
					initializeMarkerButtons();
					objectAssociatedMarker3Button.setSelected(true);
					objectAssociatedMarker3Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==16) {
					positiveLabelFlag = true;
					initializeMarkerButtons();
					objectAssociatedMarker3Button.setSelected(true);
					objectAssociatedMarker3PositiveLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==17) {
					positiveLabelFlag = false;
					initializeMarkerButtons();
					objectAssociatedMarker3Button.setSelected(true);
					objectAssociatedMarker3NegativeLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==18) {
					initializeMarkerButtons();
					objectAssociatedMarker4Button.setSelected(true);
					objectAssociatedMarker4Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==19) {
					initializeMarkerButtons();
					objectAssociatedMarker4Button.setSelected(true);
					objectAssociatedMarker4Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==20) {
					initializeMarkerButtons();
					objectAssociatedMarker4Button.setSelected(true);
					objectAssociatedMarker4Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==21) {
					initializeMarkerButtons();
					objectAssociatedMarker4Button.setSelected(true);
					objectAssociatedMarker4Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==22) {
					positiveLabelFlag = true;
					initializeMarkerButtons();
					objectAssociatedMarker4Button.setSelected(true);
					objectAssociatedMarker4PositiveLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==23) {
					positiveLabelFlag = false;
					initializeMarkerButtons();
					objectAssociatedMarker4Button.setSelected(true);
					objectAssociatedMarker4NegativeLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==24) {
					initializeMarkerButtons();
					objectAssociatedMarker5Button.setSelected(true);
					objectAssociatedMarker5Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==25) {
					initializeMarkerButtons();
					objectAssociatedMarker5Button.setSelected(true);
					objectAssociatedMarker5Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==26) {
					initializeMarkerButtons();
					objectAssociatedMarker5Button.setSelected(true);
					objectAssociatedMarker5Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==27) {
					initializeMarkerButtons();
					objectAssociatedMarker5Button.setSelected(true);
					objectAssociatedMarker5Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==28) {
					positiveLabelFlag = true;
					initializeMarkerButtons();
					objectAssociatedMarker5Button.setSelected(true);
					objectAssociatedMarker5PositiveLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==29) {
					positiveLabelFlag = false;
					initializeMarkerButtons();
					objectAssociatedMarker5Button.setSelected(true);
					objectAssociatedMarker5NegativeLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==30) {
					initializeMarkerButtons();
					objectAssociatedMarker6Button.setSelected(true);
					objectAssociatedMarker6Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==31) {
					initializeMarkerButtons();
					objectAssociatedMarker6Button.setSelected(true);
					objectAssociatedMarker6Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==32) {
					initializeMarkerButtons();
					objectAssociatedMarker6Button.setSelected(true);
					objectAssociatedMarker6Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==33) {
					initializeMarkerButtons();
					objectAssociatedMarker6Button.setSelected(true);
					objectAssociatedMarker6Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==34) {
					positiveLabelFlag = true;
					initializeMarkerButtons();
					objectAssociatedMarker6Button.setSelected(true);
					objectAssociatedMarker6PositiveLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==35) {
					positiveLabelFlag = false;
					initializeMarkerButtons();
					objectAssociatedMarker6Button.setSelected(true);
					objectAssociatedMarker6NegativeLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==36) {
					initializeMarkerButtons();
					objectAssociatedMarker7Button.setSelected(true);
					objectAssociatedMarker7Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==37) {
					initializeMarkerButtons();
					objectAssociatedMarker7Button.setSelected(true);
					objectAssociatedMarker7Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==38) {
					initializeMarkerButtons();
					objectAssociatedMarker7Button.setSelected(true);
					objectAssociatedMarker7Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==39) {
					initializeMarkerButtons();
					objectAssociatedMarker7Button.setSelected(true);
					objectAssociatedMarker7Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==40) {
					positiveLabelFlag = true;
					initializeMarkerButtons();
					objectAssociatedMarker7Button.setSelected(true);
					objectAssociatedMarker7PositiveLabelButton.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==41) {
					positiveLabelFlag = false;
					initializeMarkerButtons();
					objectAssociatedMarker7Button.setSelected(true);
					objectAssociatedMarker7NegativeLabelButton.setSelected(true);
					currentPattern = 0;
				}
			}
			else {
				if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
				currentObjectAssociatedMarker = pressedButton/6;
				initializeMarkerButtons();
				if(currentObjectAssociatedMarker==0) {
					objectAssociatedMarker1Button.setSelected(true);
					if((pressedButton - currentObjectAssociatedMarker*6)==0) {
						objectAssociatedMarker1Pattern1Button.setSelected(true);
						currentPattern = 0;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==1) {
						objectAssociatedMarker1Pattern2Button.setSelected(true);
						currentPattern = 1;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==2) {
						objectAssociatedMarker1Pattern3Button.setSelected(true);
						currentPattern = 2;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==3) {
						objectAssociatedMarker1Pattern4Button.setSelected(true);
						currentPattern = 3;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==4) {
						positiveLabelFlag = true;
						objectAssociatedMarker1PositiveLabelButton.setSelected(true);
					}
					else{
						positiveLabelFlag = false;
						objectAssociatedMarker1NegativeLabelButton.setSelected(true);
					}
					activateCurrentNucleiMarkerOverlays(0);
				}
				if(currentObjectAssociatedMarker==1) {
					objectAssociatedMarker2Button.setSelected(true);
					if((pressedButton - currentObjectAssociatedMarker*6)==0) {
						objectAssociatedMarker2Pattern1Button.setSelected(true);
						currentPattern = 0;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==1) {
						objectAssociatedMarker2Pattern2Button.setSelected(true);
						currentPattern = 1;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==2) {
						objectAssociatedMarker2Pattern3Button.setSelected(true);
						currentPattern = 2;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==3) {
						objectAssociatedMarker2Pattern4Button.setSelected(true);
						currentPattern = 3;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==4) {
						positiveLabelFlag = true;
						objectAssociatedMarker2PositiveLabelButton.setSelected(true);
					}
					else{
						positiveLabelFlag = false;
						objectAssociatedMarker2NegativeLabelButton.setSelected(true);
					}
					activateCurrentNucleiMarkerOverlays(1);
				}
				if(currentObjectAssociatedMarker==2) {
					objectAssociatedMarker3Button.setSelected(true);
					if((pressedButton - currentObjectAssociatedMarker*6)==0) {
						objectAssociatedMarker3Pattern1Button.setSelected(true);
						currentPattern = 0;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==1) {
						objectAssociatedMarker3Pattern2Button.setSelected(true);
						currentPattern = 1;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==2) {
						objectAssociatedMarker3Pattern3Button.setSelected(true);
						currentPattern = 2;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==3) {
						objectAssociatedMarker3Pattern4Button.setSelected(true);
						currentPattern = 3;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==4) {
						positiveLabelFlag = true;
						objectAssociatedMarker3PositiveLabelButton.setSelected(true);
					}
					else{
						positiveLabelFlag = false;
						objectAssociatedMarker3NegativeLabelButton.setSelected(true);
					}
					activateCurrentNucleiMarkerOverlays(2);
				}
				if(currentObjectAssociatedMarker==3) {
					objectAssociatedMarker4Button.setSelected(true);
					if((pressedButton - currentObjectAssociatedMarker*6)==0) {
						objectAssociatedMarker4Pattern1Button.setSelected(true);
						currentPattern = 0;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==1) {
						objectAssociatedMarker4Pattern2Button.setSelected(true);
						currentPattern = 1;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==2) {
						objectAssociatedMarker4Pattern3Button.setSelected(true);
						currentPattern = 2;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==3) {
						objectAssociatedMarker4Pattern4Button.setSelected(true);
						currentPattern = 3;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==4) {
						positiveLabelFlag = true;
						objectAssociatedMarker4PositiveLabelButton.setSelected(true);
					}
					else{
						positiveLabelFlag = false;
						objectAssociatedMarker4NegativeLabelButton.setSelected(true);
					}
					activateCurrentNucleiMarkerOverlays(3);
				}
				if(currentObjectAssociatedMarker==4) {
					objectAssociatedMarker5Button.setSelected(true);
					if((pressedButton - currentObjectAssociatedMarker*6)==0) {
						objectAssociatedMarker5Pattern1Button.setSelected(true);
						currentPattern = 0;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==1) {
						objectAssociatedMarker5Pattern2Button.setSelected(true);
						currentPattern = 1;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==2) {
						objectAssociatedMarker5Pattern3Button.setSelected(true);
						currentPattern = 2;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==3) {
						objectAssociatedMarker5Pattern4Button.setSelected(true);
						currentPattern = 3;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==4) {
						positiveLabelFlag = true;
						objectAssociatedMarker5PositiveLabelButton.setSelected(true);
					}
					else{
						positiveLabelFlag = false;
						objectAssociatedMarker5NegativeLabelButton.setSelected(true);
					}
					activateCurrentNucleiMarkerOverlays(4);
				}
				if(currentObjectAssociatedMarker==5) {
					objectAssociatedMarker6Button.setSelected(true);
					if((pressedButton - currentObjectAssociatedMarker*6)==0) {
						objectAssociatedMarker6Pattern1Button.setSelected(true);
						currentPattern = 0;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==1) {
						objectAssociatedMarker6Pattern2Button.setSelected(true);
						currentPattern = 1;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==2) {
						objectAssociatedMarker6Pattern3Button.setSelected(true);
						currentPattern = 2;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==3) {
						objectAssociatedMarker6Pattern4Button.setSelected(true);
						currentPattern = 3;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==4) {
						positiveLabelFlag = true;
						objectAssociatedMarker6PositiveLabelButton.setSelected(true);
					}
					else{
						positiveLabelFlag = false;
						objectAssociatedMarker6NegativeLabelButton.setSelected(true);
					}
					activateCurrentNucleiMarkerOverlays(5);
				}
				if(currentObjectAssociatedMarker==6) {
					objectAssociatedMarker7Button.setSelected(true);
					if((pressedButton - currentObjectAssociatedMarker*6)==0) {
						objectAssociatedMarker7Pattern1Button.setSelected(true);
						currentPattern = 0;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==1) {
						objectAssociatedMarker7Pattern2Button.setSelected(true);
						currentPattern = 1;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==2) {
						objectAssociatedMarker7Pattern3Button.setSelected(true);
						currentPattern = 2;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==3) {
						objectAssociatedMarker7Pattern4Button.setSelected(true);
						currentPattern = 3;
					}
					else if((pressedButton - currentObjectAssociatedMarker*6)==4) {
						positiveLabelFlag = true;
						objectAssociatedMarker7PositiveLabelButton.setSelected(true);
					}
					else{
						positiveLabelFlag = false;
						objectAssociatedMarker7NegativeLabelButton.setSelected(true);
					}
					activateCurrentNucleiMarkerOverlays(6);
				}
			}
		}
		else {
			initializeMarkerButtons();
		}
	}
	/**
	 * Remove class
	 */
	private void removeClass(int classToRemove)
	{
		JLabel label = new JLabel("Are you sure you want to remove class " + (classToRemove+1) + "?");
		scale(label);
		// make sure the user wants to remove the class
		switch ( JOptionPane.showConfirmDialog( null, label, "Class removal", JOptionPane.YES_NO_OPTION ) )
		{
		case JOptionPane.YES_OPTION:
			// remove nuclei belonging to the class to remove
			int progressIndex=0, totalNbObjectsToRemove=objectsInEachClass[classToRemove].size();
			while(objectsInEachClass[classToRemove].size()>0) {
				IJ.showProgress(progressIndex, totalNbObjectsToRemove);
				Point[] pl = objectsInEachClass[classToRemove].get(objectsInEachClass[classToRemove].size()-1);
				int xC = pl[pl.length/2].x, yC = pl[pl.length/2].y;
				int roiIdToRemove = roiFlag[xC][yC][1], overlayIdToRemove = roiFlag[xC][yC][2];
				removeRoi(classToRemove, roiIdToRemove, overlayIdToRemove);
				progressIndex++;
			}

			// if there are more than one class before removing
			if(numOfClasses>1) {
				// new number of classes
				numOfClasses--;
				// if class to remove is not the last one, all of the classes after the class to remove change id -> -1
				for(int i=classToRemove;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i+1].size();j++) {
						objectsInEachClass[i].add(objectsInEachClass[i+1].get(j));
						//Polygon pl = objectsInEachClass[i].get(j).getPolygon();
						Point[] pl = objectsInEachClass[i].get(j);
						for(int k=0;k<pl.length;k++) {
							roiFlag[pl[k].x][pl[k].y][0]--;
						}
					}
					classColors[i] = classColors[i+1];
				}
				// remove last class after id change
				objectsInEachClass[numOfClasses] = null;
				// update color
				classColors[numOfClasses] = -1;
				// remove action listener for last class
				switch (numOfClasses) {
				case 1:
					class2ColorButton.removeActionListener(listener);
					class2RemoveButton.removeActionListener(listener);
					class2Button.setSelected(false);
					break;
				case 2:
					class3ColorButton.removeActionListener(listener);
					class3RemoveButton.removeActionListener(listener);
					class3Button.setSelected(false);
					break;
				case 3:
					class4ColorButton.removeActionListener(listener);
					class4RemoveButton.removeActionListener(listener);
					class4Button.setSelected(false);
					break;
				case 4:
					class5ColorButton.removeActionListener(listener);
					class5RemoveButton.removeActionListener(listener);
					class5Button.setSelected(false);
					break;
				default:
					break;
				}
				class1Button.setSelected(true);
				currentClass = 0;
				// update panel (one class less)
				//Build GUI
				//win = new CustomWindow(displayImage);
				//win.pack();
				repaintWindow();
			}
			else {
				// reinitializa class 1
				objectsInEachClass[0] = null;
				objectsInEachClass[0] = new ArrayList<Point[]>();
			}

			// display update
			displayImage.setOverlay(overlay);
			displayImage.updateAndDraw();
			break;
		case JOptionPane.NO_OPTION:
			return;
		}
	}			
	/**
	 * Remove whole area
	 */
	private void removeWholeArea(int areaToRemove)
	{
		JLabel label = new JLabel("Are you sure you want to remove area " + (areaToRemove+1) + "?");
		scale(label);
		// make sure the user wants to remove the class
		switch ( JOptionPane.showConfirmDialog( null, label, "Region removal", JOptionPane.YES_NO_OPTION ) )
		{
		case JOptionPane.YES_OPTION:
			// remove nuclei belonging to the class to remove
			int progressIndex=0, totalNbAreasToRemove=areasInEachClass[areaToRemove].size();
			while(areasInEachClass[areaToRemove].size()>0) {
				IJ.showProgress(progressIndex, totalNbAreasToRemove);
				Point[] pl = areasInEachClass[areaToRemove].get(0);
				int xC = pl[pl.length/2].x, yC = pl[pl.length/2].y;
				int roiIdToRemove = areaFlag[xC][yC][1], overlayIdToRemove = areaFlag[xC][yC][2];
				removeAreaRoi(areaToRemove, roiIdToRemove, overlayIdToRemove);
				progressIndex++;
			}

			// if there are more than one class before removing
			if(numOfAreas>1) {
				// new number of classes
				numOfAreas--;
				// if class to remove is not the last one, all of the classes after the class to remove change id -> -1
				for(int i=areaToRemove;i<numOfAreas;i++) {
					for(int j=0;j<areasInEachClass[i+1].size();j++) {
						areasInEachClass[i].add(areasInEachClass[i+1].get(j));
						Point[] pl = areasInEachClass[i].get(j);
						for(int k=0;k<pl.length;k++) {
							areaFlag[pl[k].x][pl[k].y][0]--;
						}
					}
					areaColors[i] = areaColors[i+1];
				}
				// remove last class after id change
				areasInEachClass[numOfAreas] = null;
				// update color
				areaColors[numOfAreas] = -1;
				// remove action listener for last class
				switch (numOfAreas) {
				case 1:
					area2ColorButton.removeActionListener(listener);
					area2RemoveButton.removeActionListener(listener);
					area2Button.setSelected(false);
					break;
				case 2:
					area3ColorButton.removeActionListener(listener);
					area3RemoveButton.removeActionListener(listener);
					area3Button.setSelected(false);
					break;
				case 3:
					area4ColorButton.removeActionListener(listener);
					area4RemoveButton.removeActionListener(listener);
					area4Button.setSelected(false);
					break;
				case 4:
					area5ColorButton.removeActionListener(listener);
					area5RemoveButton.removeActionListener(listener);
					area5Button.setSelected(false);
					break;
				default:
					break;
				}
				area1Button.setSelected(true);
				currentArea = 0;
				// update panel (one class less)
				//Build GUI
				//win = new CustomWindow(displayImage);
				//win.pack();
				repaintWindow();
			}
			else {
				// reinitializa class 1
				areasInEachClass[0] = null;
				areasInEachClass[0] = new ArrayList<Point[]>();
			}

			// display update
			displayImage.setOverlay(overlay);
			displayImage.updateAndDraw();
			break;
		case JOptionPane.NO_OPTION:
			return;
		}
	}			
	/**
	 * Modify the roi color for a given class
	 */
	private boolean updateRoiClassColorWindow(int roiClass)
	{
		// button initialization
		redCheck.setSelected(false);
		greenCheck.setSelected(false);
		blueCheck.setSelected(false);
		yellowCheck.setSelected(false);
		magentaCheck.setSelected(false);
		cyanCheck.setSelected(false);
		orangeCheck.setSelected(false);
		pinkCheck.setSelected(false);
		blackCheck.setSelected(false);
		grayCheck.setSelected(false);
		whiteCheck.setSelected(false);


		switch (classColors[roiClass]) {
		case 0:
			redCheck.setSelected(true);
			break;
		case 1:
			greenCheck.setSelected(true);
			break;
		case 2:
			blueCheck.setSelected(true);
			break;
		case 3:
			yellowCheck.setSelected(true);
			break;
		case 4:
			magentaCheck.setSelected(true);
			break;
		case 5:
			cyanCheck.setSelected(true);
			break;
		case 6:
			orangeCheck.setSelected(true);
			break;
		case 7:
			pinkCheck.setSelected(true);
			break;
		case 8:
			blackCheck.setSelected(true);
			break;
		case 9:
			grayCheck.setSelected(true);
			break;
		case 10:
			whiteCheck.setSelected(true);
			break;
		default:
			break;
		}

		ButtonGroup bg=new ButtonGroup();    
		bg.add(redCheck);bg.add(greenCheck);bg.add(blueCheck);bg.add(yellowCheck);
		bg.add(magentaCheck);bg.add(cyanCheck);bg.add(orangeCheck);bg.add(pinkCheck);
		bg.add(blackCheck);bg.add(grayCheck);bg.add(whiteCheck);

		JPanel colorPanel = new JPanel();
		colorPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout = new GridBagLayout();
		GridBagConstraints colorPanelConstraints = new GridBagConstraints();
		colorPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints.gridwidth = 1;
		colorPanelConstraints.gridheight = 1;
		colorPanelConstraints.gridx = 0;
		colorPanelConstraints.gridy = 0;
		colorPanel.setLayout(colorPanelLayout);
		colorPanel.add(redCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(greenCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(blueCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(yellowCheck,colorPanelConstraints);
		colorPanelConstraints.gridy++;
		colorPanelConstraints.gridx = 0;
		colorPanel.add(magentaCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(cyanCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(orangeCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(pinkCheck,colorPanelConstraints);
		colorPanelConstraints.gridy++;
		colorPanelConstraints.gridx = 0;
		colorPanel.add(blackCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(grayCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(whiteCheck,colorPanelConstraints);

		GenericDialogPlus gd = new GenericDialogPlus("ROI color settings");
		gd.addMessage("New color for class " + (roiClass+1) + ":");
		gd.addComponent(colorPanel);
		gd.showDialog();

		if (gd.wasCanceled())
			return false;

		return true;
	}
	/**
	 * Add new class in the panel (up to MAX_NUM_CLASSES)
	 */
	private void addNewClass() 
	{
		if(numOfClasses == MAX_NUM_CLASSES)
		{
			IJ.showMessage("Maximum number of classes", "Sorry, maximum number of classes has been reached");
			return;
		}

		// Add new class label and list
		win.addClass();

		repaintWindow();
	}
	/**
	 * Modify the color for a given area
	 */
	private boolean updateAreaColorWindow(int roiClass)
	{
		// button initialization
		redCheck.setSelected(false);
		greenCheck.setSelected(false);
		blueCheck.setSelected(false);
		yellowCheck.setSelected(false);
		magentaCheck.setSelected(false);
		cyanCheck.setSelected(false);
		whiteCheck.setSelected(false);


		switch (areaColors[roiClass]) {
		case 0:
			redCheck.setSelected(true);
			break;
		case 1:
			greenCheck.setSelected(true);
			break;
		case 2:
			blueCheck.setSelected(true);
			break;
		case 3:
			yellowCheck.setSelected(true);
			break;
		case 4:
			magentaCheck.setSelected(true);
			break;
		case 5:
			cyanCheck.setSelected(true);
			break;
		case 8:
			whiteCheck.setSelected(true);
			break;
		default:
			break;
		}

		ButtonGroup bg=new ButtonGroup();    
		bg.add(redCheck);bg.add(greenCheck);bg.add(blueCheck);bg.add(yellowCheck);
		bg.add(magentaCheck);bg.add(cyanCheck);bg.add(whiteCheck);

		JPanel colorPanel = new JPanel();
		colorPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout = new GridBagLayout();
		GridBagConstraints colorPanelConstraints = new GridBagConstraints();
		colorPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints.gridwidth = 1;
		colorPanelConstraints.gridheight = 1;
		colorPanelConstraints.gridx = 0;
		colorPanelConstraints.gridy = 0;
		colorPanel.setLayout(colorPanelLayout);
		colorPanel.add(redCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(greenCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(blueCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(yellowCheck,colorPanelConstraints);
		colorPanelConstraints.gridy++;
		colorPanelConstraints.gridx = 0;
		colorPanel.add(magentaCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(cyanCheck,colorPanelConstraints);
		colorPanelConstraints.gridx++;
		colorPanel.add(whiteCheck,colorPanelConstraints);

		GenericDialogPlus gd = new GenericDialogPlus("Region color settings");
		gd.addMessage("New color for area " + (roiClass+1) + ":");
		gd.addComponent(colorPanel);
		gd.showDialog();

		if (gd.wasCanceled())
			return false;

		return true;
	}
	/**
	 * Add new class in the panel (up to MAX_NUM_CLASSES)
	 */
	private void addNewArea() 
	{
		if(numOfAreas == MAX_NUM_CLASSES)
		{
			IJ.showMessage("Maximum number of areas", "Sorry, maximum number of classes has been reached");
			return;
		}

		// Add new class label and list
		win.addAreaClass();

		repaintWindow();
	}
	/**
	 * Modify the pattern colors for a given marker
	 */
	private boolean updatePatternColorsWindow(int marker)
	{
		// button initialization
		redCheck1.setSelected(false);
		greenCheck1.setSelected(false);
		blueCheck1.setSelected(false);
		yellowCheck1.setSelected(false);
		magentaCheck1.setSelected(false);
		cyanCheck1.setSelected(false);
		orangeCheck1.setSelected(false);
		pinkCheck1.setSelected(false);
		blackCheck1.setSelected(false);
		grayCheck1.setSelected(false);
		whiteCheck1.setSelected(false);
		redCheck2.setSelected(false);
		greenCheck2.setSelected(false);
		blueCheck2.setSelected(false);
		yellowCheck2.setSelected(false);
		magentaCheck2.setSelected(false);
		cyanCheck2.setSelected(false);
		orangeCheck2.setSelected(false);
		pinkCheck2.setSelected(false);
		blackCheck2.setSelected(false);
		grayCheck2.setSelected(false);
		whiteCheck2.setSelected(false);
		redCheck3.setSelected(false);
		greenCheck3.setSelected(false);
		blueCheck3.setSelected(false);
		yellowCheck3.setSelected(false);
		magentaCheck3.setSelected(false);
		cyanCheck3.setSelected(false);
		orangeCheck3.setSelected(false);
		pinkCheck3.setSelected(false);
		blackCheck3.setSelected(false);
		grayCheck3.setSelected(false);
		whiteCheck3.setSelected(false);
		redCheck4.setSelected(false);
		greenCheck4.setSelected(false);
		blueCheck4.setSelected(false);
		yellowCheck4.setSelected(false);
		magentaCheck4.setSelected(false);
		cyanCheck4.setSelected(false);
		orangeCheck4.setSelected(false);
		pinkCheck4.setSelected(false);
		blackCheck4.setSelected(false);
		grayCheck4.setSelected(false);
		whiteCheck4.setSelected(false);


		switch (objectAssociatedMarkersColors[marker][0]) {
		case 0:
			redCheck1.setSelected(true);
			break;
		case 1:
			greenCheck1.setSelected(true);
			break;
		case 2:
			blueCheck1.setSelected(true);
			break;
		case 3:
			yellowCheck1.setSelected(true);
			break;
		case 4:
			magentaCheck1.setSelected(true);
			break;
		case 5:
			cyanCheck1.setSelected(true);
			break;
		case 6:
			orangeCheck1.setSelected(true);
			break;
		case 7:
			pinkCheck1.setSelected(true);
			break;
		case 8:
			blackCheck1.setSelected(true);
			break;
		case 9:
			grayCheck1.setSelected(true);
			break;
		case 10:
			whiteCheck1.setSelected(true);
			break;
		default:
			break;
		}
		switch (objectAssociatedMarkersColors[marker][1]) {
		case 0:
			redCheck2.setSelected(true);
			break;
		case 1:
			greenCheck2.setSelected(true);
			break;
		case 2:
			blueCheck2.setSelected(true);
			break;
		case 3:
			yellowCheck2.setSelected(true);
			break;
		case 4:
			magentaCheck2.setSelected(true);
			break;
		case 5:
			cyanCheck2.setSelected(true);
			break;
		case 6:
			orangeCheck2.setSelected(true);
			break;
		case 7:
			pinkCheck2.setSelected(true);
			break;
		case 8:
			blackCheck2.setSelected(true);
			break;
		case 9:
			grayCheck2.setSelected(true);
			break;
		case 10:
			whiteCheck2.setSelected(true);
			break;
		default:
			break;
		}
		switch (objectAssociatedMarkersColors[marker][2]) {
		case 0:
			redCheck3.setSelected(true);
			break;
		case 1:
			greenCheck3.setSelected(true);
			break;
		case 2:
			blueCheck3.setSelected(true);
			break;
		case 3:
			yellowCheck3.setSelected(true);
			break;
		case 4:
			magentaCheck3.setSelected(true);
			break;
		case 5:
			cyanCheck3.setSelected(true);
			break;
		case 6:
			orangeCheck3.setSelected(true);
			break;
		case 7:
			pinkCheck3.setSelected(true);
			break;
		case 8:
			blackCheck3.setSelected(true);
			break;
		case 9:
			grayCheck3.setSelected(true);
			break;
		case 10:
			whiteCheck3.setSelected(true);
			break;
		default:
			break;
		}
		switch (objectAssociatedMarkersColors[marker][3]) {
		case 0:
			redCheck4.setSelected(true);
			break;
		case 1:
			greenCheck4.setSelected(true);
			break;
		case 2:
			blueCheck4.setSelected(true);
			break;
		case 3:
			yellowCheck4.setSelected(true);
			break;
		case 4:
			magentaCheck4.setSelected(true);
			break;
		case 5:
			cyanCheck4.setSelected(true);
			break;
		case 6:
			orangeCheck4.setSelected(true);
			break;
		case 7:
			pinkCheck4.setSelected(true);
			break;
		case 8:
			blackCheck4.setSelected(true);
			break;
		case 9:
			grayCheck4.setSelected(true);
			break;
		case 10:
			whiteCheck4.setSelected(true);
			break;
		default:
			break;
		}

		ButtonGroup bg1=new ButtonGroup(),bg2=new ButtonGroup(),bg3=new ButtonGroup(),bg4=new ButtonGroup();    
		bg1.add(redCheck1);bg1.add(greenCheck1);bg1.add(blueCheck1);bg1.add(yellowCheck1);
		bg1.add(magentaCheck1);bg1.add(cyanCheck1);bg1.add(orangeCheck1);bg1.add(pinkCheck1);
		bg1.add(blackCheck1);bg1.add(grayCheck1);bg1.add(whiteCheck1);
		bg2.add(redCheck2);bg2.add(greenCheck2);bg2.add(blueCheck2);bg2.add(yellowCheck2);
		bg2.add(magentaCheck2);bg2.add(cyanCheck2);bg2.add(orangeCheck2);bg2.add(pinkCheck2);
		bg2.add(blackCheck2);bg2.add(grayCheck2);bg2.add(whiteCheck2);
		bg3.add(redCheck3);bg3.add(greenCheck3);bg3.add(blueCheck3);bg3.add(yellowCheck3);
		bg3.add(magentaCheck3);bg3.add(cyanCheck3);bg3.add(orangeCheck3);bg3.add(pinkCheck3);
		bg3.add(blackCheck3);bg3.add(grayCheck3);bg3.add(whiteCheck3);
		bg4.add(redCheck4);bg4.add(greenCheck4);bg4.add(blueCheck4);bg4.add(yellowCheck4);
		bg4.add(magentaCheck4);bg4.add(cyanCheck4);bg4.add(orangeCheck4);bg4.add(pinkCheck4);
		bg4.add(blackCheck4);bg4.add(grayCheck4);bg4.add(whiteCheck4);

		JPanel colorPanel1 = new JPanel();
		colorPanel1.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout1 = new GridBagLayout();
		GridBagConstraints colorPanelConstraints1 = new GridBagConstraints();
		colorPanelConstraints1.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints1.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints1.gridwidth = 1;
		colorPanelConstraints1.gridheight = 1;
		colorPanelConstraints1.gridx = 0;
		colorPanelConstraints1.gridy = 0;
		colorPanel1.setLayout(colorPanelLayout1);
		colorPanel1.add(redCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(greenCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(blueCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(yellowCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridy++;
		colorPanelConstraints1.gridx = 0;
		colorPanel1.add(magentaCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(cyanCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(orangeCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(pinkCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridy++;
		colorPanelConstraints1.gridx = 0;
		colorPanel1.add(blackCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(grayCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(whiteCheck1,colorPanelConstraints1);
		JPanel colorPanel2 = new JPanel();
		colorPanel2.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout2 = new GridBagLayout();
		GridBagConstraints colorPanelConstraints2 = new GridBagConstraints();
		colorPanelConstraints2.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints2.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints2.gridwidth = 1;
		colorPanelConstraints2.gridheight = 1;
		colorPanelConstraints2.gridx = 0;
		colorPanelConstraints2.gridy = 0;
		colorPanel2.setLayout(colorPanelLayout2);
		colorPanel2.add(redCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(greenCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(blueCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(yellowCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridy++;
		colorPanelConstraints2.gridx = 0;
		colorPanel2.add(magentaCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(cyanCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(orangeCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(pinkCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridy++;
		colorPanelConstraints2.gridx = 0;
		colorPanel2.add(blackCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(grayCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(whiteCheck2,colorPanelConstraints2);
		JPanel colorPanel3 = new JPanel();
		colorPanel3.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout3 = new GridBagLayout();
		GridBagConstraints colorPanelConstraints3 = new GridBagConstraints();
		colorPanelConstraints3.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints3.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints3.gridwidth = 1;
		colorPanelConstraints3.gridheight = 1;
		colorPanelConstraints3.gridx = 0;
		colorPanelConstraints3.gridy = 0;
		colorPanel3.setLayout(colorPanelLayout3);
		colorPanel3.add(redCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(greenCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(blueCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(yellowCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridy++;
		colorPanelConstraints3.gridx = 0;
		colorPanel3.add(magentaCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(cyanCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(orangeCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(pinkCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridy++;
		colorPanelConstraints3.gridx = 0;
		colorPanel3.add(blackCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(grayCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(whiteCheck3,colorPanelConstraints3);
		JPanel colorPanel4 = new JPanel();
		colorPanel4.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout4 = new GridBagLayout();
		GridBagConstraints colorPanelConstraints4 = new GridBagConstraints();
		colorPanelConstraints4.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints4.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints4.gridwidth = 1;
		colorPanelConstraints4.gridheight = 1;
		colorPanelConstraints4.gridx = 0;
		colorPanelConstraints4.gridy = 0;
		colorPanel4.setLayout(colorPanelLayout4);
		colorPanel4.add(redCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(greenCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(blueCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(yellowCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridy++;
		colorPanelConstraints4.gridx = 0;
		colorPanel4.add(magentaCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(cyanCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(orangeCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(pinkCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridy++;
		colorPanelConstraints4.gridx = 0;
		colorPanel4.add(blackCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(grayCheck4,colorPanelConstraints4);
		colorPanelConstraints4.gridx++;
		colorPanel4.add(whiteCheck4,colorPanelConstraints4);



		GenericDialogPlus gd = new GenericDialogPlus("Marker pattern color settings");
		gd.addMessage("New color for pattern 1 of marker " + (marker+1) + ":");
		gd.addComponent(colorPanel1);
		gd.addMessage("New color for pattern 2 of marker " + (marker+1) + ":");
		gd.addComponent(colorPanel2);
		gd.addMessage("New color for pattern 3 of marker " + (marker+1) + ":");
		gd.addComponent(colorPanel3);
		gd.addMessage("New color for pattern 4 of marker " + (marker+1) + ":");
		gd.addComponent(colorPanel4);

		gd.showDialog();

		if (gd.wasCanceled())
			return false;

		return true;
	}

	/**
	 * Modify the pattern colors for a given marker
	 */
	private boolean updateMLColorsWindow(int marker)
	{
		// button initialization
		redCheck1.setSelected(false);
		greenCheck1.setSelected(false);
		blueCheck1.setSelected(false);
		yellowCheck1.setSelected(false);
		magentaCheck1.setSelected(false);
		cyanCheck1.setSelected(false);
		orangeCheck1.setSelected(false);
		pinkCheck1.setSelected(false);
		blackCheck1.setSelected(false);
		grayCheck1.setSelected(false);
		whiteCheck1.setSelected(false);
		redCheck2.setSelected(false);
		greenCheck2.setSelected(false);
		blueCheck2.setSelected(false);
		yellowCheck2.setSelected(false);
		magentaCheck2.setSelected(false);
		cyanCheck2.setSelected(false);
		orangeCheck2.setSelected(false);
		pinkCheck2.setSelected(false);
		blackCheck2.setSelected(false);
		grayCheck2.setSelected(false);
		whiteCheck2.setSelected(false);
		redCheck3.setSelected(false);
		greenCheck3.setSelected(false);
		blueCheck3.setSelected(false);
		yellowCheck3.setSelected(false);
		magentaCheck3.setSelected(false);
		cyanCheck3.setSelected(false);
		orangeCheck3.setSelected(false);
		pinkCheck3.setSelected(false);
		blackCheck3.setSelected(false);
		grayCheck3.setSelected(false);
		whiteCheck3.setSelected(false);

		switch (objectAssociatedMarkersMLColors[marker][0]) {
		case 0:
			redCheck1.setSelected(true);
			break;
		case 1:
			greenCheck1.setSelected(true);
			break;
		case 2:
			blueCheck1.setSelected(true);
			break;
		case 3:
			yellowCheck1.setSelected(true);
			break;
		case 4:
			magentaCheck1.setSelected(true);
			break;
		case 5:
			cyanCheck1.setSelected(true);
			break;
		case 6:
			orangeCheck1.setSelected(true);
			break;
		case 7:
			pinkCheck1.setSelected(true);
			break;
		case 8:
			blackCheck1.setSelected(true);
			break;
		case 9:
			grayCheck1.setSelected(true);
			break;
		case 10:
			whiteCheck1.setSelected(true);
			break;
		default:
			break;
		}
		switch (objectAssociatedMarkersMLColors[marker][1]) {
		case 0:
			redCheck2.setSelected(true);
			break;
		case 1:
			greenCheck2.setSelected(true);
			break;
		case 2:
			blueCheck2.setSelected(true);
			break;
		case 3:
			yellowCheck2.setSelected(true);
			break;
		case 4:
			magentaCheck2.setSelected(true);
			break;
		case 5:
			cyanCheck2.setSelected(true);
			break;
		case 6:
			orangeCheck2.setSelected(true);
			break;
		case 7:
			pinkCheck2.setSelected(true);
			break;
		case 8:
			blackCheck2.setSelected(true);
			break;
		case 9:
			grayCheck2.setSelected(true);
			break;
		case 10:
			whiteCheck2.setSelected(true);
			break;
		default:
			break;
		}
		switch (objectAssociatedMarkersMLColors[marker][2]) {
		case 0:
			redCheck3.setSelected(true);
			break;
		case 1:
			greenCheck3.setSelected(true);
			break;
		case 2:
			blueCheck3.setSelected(true);
			break;
		case 3:
			yellowCheck3.setSelected(true);
			break;
		case 4:
			magentaCheck3.setSelected(true);
			break;
		case 5:
			cyanCheck3.setSelected(true);
			break;
		case 6:
			orangeCheck3.setSelected(true);
			break;
		case 7:
			pinkCheck3.setSelected(true);
			break;
		case 8:
			blackCheck3.setSelected(true);
			break;
		case 9:
			grayCheck3.setSelected(true);
			break;
		case 10:
			whiteCheck3.setSelected(true);
			break;
		default:
			break;
		}

		ButtonGroup bg1=new ButtonGroup(),bg2=new ButtonGroup(),bg3=new ButtonGroup();    
		bg1.add(redCheck1);bg1.add(greenCheck1);bg1.add(blueCheck1);bg1.add(yellowCheck1);
		bg1.add(magentaCheck1);bg1.add(cyanCheck1);bg1.add(orangeCheck1);bg1.add(pinkCheck1);
		bg1.add(blackCheck1);bg1.add(grayCheck1);bg1.add(whiteCheck1);
		bg2.add(redCheck2);bg2.add(greenCheck2);bg2.add(blueCheck2);bg2.add(yellowCheck2);
		bg2.add(magentaCheck2);bg2.add(cyanCheck2);bg2.add(orangeCheck2);bg2.add(pinkCheck2);
		bg2.add(blackCheck2);bg2.add(grayCheck2);bg2.add(whiteCheck2);
		bg3.add(redCheck3);bg3.add(greenCheck3);bg3.add(blueCheck3);bg3.add(yellowCheck3);
		bg3.add(magentaCheck3);bg3.add(cyanCheck3);bg3.add(orangeCheck3);bg3.add(pinkCheck3);
		bg3.add(blackCheck3);bg3.add(grayCheck3);bg3.add(whiteCheck3);
		
		JPanel colorPanel1 = new JPanel();
		colorPanel1.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout1 = new GridBagLayout();
		GridBagConstraints colorPanelConstraints1 = new GridBagConstraints();
		colorPanelConstraints1.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints1.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints1.gridwidth = 1;
		colorPanelConstraints1.gridheight = 1;
		colorPanelConstraints1.gridx = 0;
		colorPanelConstraints1.gridy = 0;
		colorPanel1.setLayout(colorPanelLayout1);
		colorPanel1.add(redCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(greenCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(blueCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(yellowCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridy++;
		colorPanelConstraints1.gridx = 0;
		colorPanel1.add(magentaCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(cyanCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(orangeCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(pinkCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridy++;
		colorPanelConstraints1.gridx = 0;
		colorPanel1.add(blackCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(grayCheck1,colorPanelConstraints1);
		colorPanelConstraints1.gridx++;
		colorPanel1.add(whiteCheck1,colorPanelConstraints1);
		JPanel colorPanel2 = new JPanel();
		colorPanel2.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout2 = new GridBagLayout();
		GridBagConstraints colorPanelConstraints2 = new GridBagConstraints();
		colorPanelConstraints2.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints2.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints2.gridwidth = 1;
		colorPanelConstraints2.gridheight = 1;
		colorPanelConstraints2.gridx = 0;
		colorPanelConstraints2.gridy = 0;
		colorPanel2.setLayout(colorPanelLayout2);
		colorPanel2.add(redCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(greenCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(blueCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(yellowCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridy++;
		colorPanelConstraints2.gridx = 0;
		colorPanel2.add(magentaCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(cyanCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(orangeCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(pinkCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridy++;
		colorPanelConstraints2.gridx = 0;
		colorPanel2.add(blackCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(grayCheck2,colorPanelConstraints2);
		colorPanelConstraints2.gridx++;
		colorPanel2.add(whiteCheck2,colorPanelConstraints2);
		JPanel colorPanel3 = new JPanel();
		colorPanel3.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout colorPanelLayout3 = new GridBagLayout();
		GridBagConstraints colorPanelConstraints3 = new GridBagConstraints();
		colorPanelConstraints3.anchor = GridBagConstraints.NORTHWEST;
		colorPanelConstraints3.fill = GridBagConstraints.HORIZONTAL;
		colorPanelConstraints3.gridwidth = 1;
		colorPanelConstraints3.gridheight = 1;
		colorPanelConstraints3.gridx = 0;
		colorPanelConstraints3.gridy = 0;
		colorPanel3.setLayout(colorPanelLayout3);
		colorPanel3.add(redCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(greenCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(blueCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(yellowCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridy++;
		colorPanelConstraints3.gridx = 0;
		colorPanel3.add(magentaCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(cyanCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(orangeCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(pinkCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridy++;
		colorPanelConstraints3.gridx = 0;
		colorPanel3.add(blackCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(grayCheck3,colorPanelConstraints3);
		colorPanelConstraints3.gridx++;
		colorPanel3.add(whiteCheck3,colorPanelConstraints3);

		GenericDialogPlus gd = new GenericDialogPlus("Machine learning color settings");
		gd.addMessage("New color for positively labelled marker " + (marker+1) + ":");
		gd.addComponent(colorPanel1);
		gd.addMessage("New color for negatively labelled marker " + (marker+1) + ":");
		gd.addComponent(colorPanel2);
		gd.addMessage("New color for positively estimated marker " + (marker+1) + ":");
		gd.addComponent(colorPanel3);

		gd.showDialog();

		if (gd.wasCanceled())
			return false;

		return true;
	}

	/**
	 * Add new marker in the panel
	 */
	private boolean addNewMarker() 
	{
		if(numOfObjectAssociatedMarkers == MAX_NUM_MARKERS)
		{
			IJ.showMessage("Maximum number of markers", "Sorry, maximum number of markers has been reached");
			return false;
		}

		// Add new class label and list
		win.addMarker();

		repaintWindow();

		return true;

	}
	/**
	 * Remove current object associated marker
	 */
	private void removeObjectAssociatedMarkerForML(int markerToRemove) {
		for(int p=0;p<4;p++) {
			while(positiveNucleiForEachMarker[markerToRemove][p].size()>0) {
				positiveNucleiForEachMarker[markerToRemove][p].remove(0);
			}
		}
	}
	/**
	 * Remove marker
	 */
	private void deleteObjectAssociatedMarker(int markerToRemove) {
		// remove marker identifications belonging to the marker to remove for each pattern
		initializeMarkerButtons();
		if(currentObjectAssociatedMarker>(-1)) {removeMarkersFromOverlay();}
		for(int p=0;p<4;p++) {
			while(positiveNucleiForEachMarker[markerToRemove][p].size()>0) {
				positiveNucleiForEachMarker[markerToRemove][p].remove(0);
			}
		}
		// remove labeled nuclei if ML
		if(methodToIdentifyObjectAssociatedMarkers[markerToRemove]==2){
			while(positivelyLabelledNucleiForEachMarker[markerToRemove].size()>0) {
				positivelyLabelledNucleiForEachMarker[markerToRemove].remove(0);
			}
			while(negativelyLabelledNucleiForEachMarker[markerToRemove].size()>0) {
				negativelyLabelledNucleiForEachMarker[markerToRemove].remove(0);
			}
			while(featuresForEachMarker[markerToRemove].size()>0) {
				featuresForEachMarker[markerToRemove].remove(0);
			}
		}
		// update number of markers
		numOfObjectAssociatedMarkers--;

		// if marker to remove is not the last one, all of the markers after the marker to remove change id -> -1
		for(int i=markerToRemove;i<numOfObjectAssociatedMarkers;i++) {
			// copy marker i+1 to marker i
			for(int p=0;p<4;p++) {
				for(int j=0;j<positiveNucleiForEachMarker[i+1][p].size();j++) {
					positiveNucleiForEachMarker[i][p].add(positiveNucleiForEachMarker[i+1][p].get(j));
				}
				objectAssociatedMarkersColors[i][p] = objectAssociatedMarkersColors[i+1][p];
				methodToIdentifyObjectAssociatedMarkers[i] = methodToIdentifyObjectAssociatedMarkers[i+1];
				markerCellcompartment[i] = markerCellcompartment[i+1];
				channelsForObjectAssociatedMarkers[i] = channelsForObjectAssociatedMarkers[i+1];
				thresholdsForObjectAssociatedMarkers[i][0] = thresholdsForObjectAssociatedMarkers[i+1][0];
				thresholdsForObjectAssociatedMarkers[i][1] = thresholdsForObjectAssociatedMarkers[i+1][1];
				// transfer labeled nuclei if ML
				if(methodToIdentifyObjectAssociatedMarkers[i+1]==2){
					for(int j=0;j<positivelyLabelledNucleiForEachMarker[i+1].size();j++) {
						positivelyLabelledNucleiForEachMarker[i].add(positivelyLabelledNucleiForEachMarker[i+1].get(j));
					}
					for(int j=0;j<negativelyLabelledNucleiForEachMarker[i+1].size();j++) {
						negativelyLabelledNucleiForEachMarker[i].add(negativelyLabelledNucleiForEachMarker[i+1].get(j));
					}
					for(int j=0;j<featuresForEachMarker[i+1].size();j++) {
						featuresForEachMarker[i].add(featuresForEachMarker[i+1].get(j));
					}
				}
			}
			// delete marker i+1
			for(int p=0;p<4;p++) {
				while(positiveNucleiForEachMarker[i+1][p].size()>0) {
					positiveNucleiForEachMarker[i+1][p].remove(0);
				}
			}
			if(methodToIdentifyObjectAssociatedMarkers[i+1]==2){
				while(positivelyLabelledNucleiForEachMarker[i+1].size()>0) {
					positivelyLabelledNucleiForEachMarker[i+1].remove(0);
				}
				while(negativelyLabelledNucleiForEachMarker[i+1].size()>0) {
					negativelyLabelledNucleiForEachMarker[i+1].remove(0);
				}
				while(featuresForEachMarker[i+1].size()>0) {
					featuresForEachMarker[i+1].remove(0);
				}
			}
			
		}

		// remove action listener for last class
		switch (numOfObjectAssociatedMarkers) {
		case 0:
			removeMarker1ButtonFromListener();
			break;
		case 1:
			removeMarker2ButtonFromListener();
			break;
		case 2:
			removeMarker3ButtonFromListener();
			break;
		case 3:
			removeMarker4ButtonFromListener();
			break;
		case 4:
			removeMarker5ButtonFromListener();
			break;
		case 5:
			removeMarker6ButtonFromListener();
			break;
		case 6:
			removeMarker7ButtonFromListener();
			break;
		default:
			break;
		}

		// update marker associated parameters
		for(byte p=0;p<4;p++) {
			objectAssociatedMarkersColors[numOfObjectAssociatedMarkers][p] = (byte)(p+4);
		}
		markerCellcompartment[numOfObjectAssociatedMarkers] = 0;
		methodToIdentifyObjectAssociatedMarkers[numOfObjectAssociatedMarkers] = 0;
		if(methodToIdentifyObjectAssociatedMarkers[numOfObjectAssociatedMarkers]>0){
			channelsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers] = -1;
			if(methodToIdentifyObjectAssociatedMarkers[numOfObjectAssociatedMarkers]==1){
				thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers][0] = -1;
				thresholdsForObjectAssociatedMarkers[numOfObjectAssociatedMarkers][1] = -1;
			}
		}
		currentObjectAssociatedMarker = -1;
		currentPattern = -1;

		// update panel (one class less)
		//Build GUI
		repaintWindow();
		
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
	}
	private void removeObjectAssociatedMarker(int markerToRemove)
	{
		JLabel label = new JLabel("Are you sure you want to remove marker " + (markerToRemove+1) + "?");
		scale(label);
		// make sure the user wants to remove the marker
		switch ( JOptionPane.showConfirmDialog( null, label, "Marker removal", JOptionPane.YES_NO_OPTION ) )
		{
		case JOptionPane.YES_OPTION:
			deleteObjectAssociatedMarker(markerToRemove);
			break;
		case JOptionPane.NO_OPTION:
			return;
		}
	}	
	/**
	 * Train classifier to estimate markers associated objects and process
	 */
	void train(int markerToBeProcessed){
		boolean positiveF=false, negativeF=false;;
		if(featuresForEachMarker[markerToBeProcessed].size()>0){
			for(int i=0;i<featuresForEachMarker[markerToBeProcessed].size();i++){
				double[] currentFeatures = featuresForEachMarker[markerToBeProcessed].get(i);
				if(currentFeatures[currentFeatures.length-1]==0){
					positiveF = true;
				}
				else if(currentFeatures[currentFeatures.length-1]==1){
					negativeF = true;
				}
			}
		}
		if(!positiveF){
			if((positivelyLabelledNucleiForEachMarker[markerToBeProcessed].size()==0)){
				IJ.showMessage("Label positive cells", "You need to label positive cells for marker " + (markerToBeProcessed+1));
				addObjectsToOverlay();
				return;
			}
		}
		if(!negativeF){
			if(negativelyLabelledNucleiForEachMarker[markerToBeProcessed].size()==0){
				IJ.showMessage("Label negative cells", "You need to label negative cells for marker " + (markerToBeProcessed+1));
				addObjectsToOverlay();
				return;
			}
		}

		// classifier creation
		markerClassifier mc = new markerClassifier();
		// define the number of features
		mc.defineNbFeatures(nbFeatures);
		// classifier initialization
		// extract cell component needed for current marker
		List<Polygon> [] cellComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];
		for(int i=0;i<numOfClasses;i++) {
			cellComponentInEachClass[i] = new ArrayList<Polygon>();
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				Polygon fp = new Polygon();
				cellComponentInEachClass[i].add(fp);
			}
		}

		if(markerCellcompartment[markerToBeProcessed]==0) {
			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(nuclearComponent[i][x][y]>0) {
							cellComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
						}
					}
				}
			}
		}
		else if(markerCellcompartment[markerToBeProcessed]==1) {
			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			if(!innerNuclearComponentFlag){
				computeInnerNuclearComponent();
				innerNuclearComponentFlag = true;
			}
			if(!membranarComponentFlag){
				computeMembranarComponent();
				membranarComponentFlag = true;
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(membranarComponent[i][x][y]>0) {
							cellComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
						}
					}
				}
			}
		}
		else if(markerCellcompartment[markerToBeProcessed]==2) {
			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			if(!innerNuclearComponentFlag){
				computeInnerNuclearComponent();
				innerNuclearComponentFlag = true;
			}
			if(!cytoplasmicComponentFlag){
				computeCytoplasmicComponent();
				cytoplasmicComponentFlag = true;
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(cytoplasmicComponent[i][x][y]>0) {
							cellComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
						}
					}
				}
			}
		}

		// get channel
		ImageProcessor ipt = displayImage.getStack().getProcessor(channelsForObjectAssociatedMarkers[markerToBeProcessed]);

		// create testing dataset
		mc.initializeTestingDataset();

		if(!rt_nuclearML_flag){
			int initialMeasurements = Analyzer.getMeasurements(),
					measurementsForFeatures = Measurements.CIRCULARITY;
			Analyzer.setMeasurements(measurementsForFeatures);

			ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
			stack.addSlice(ipt);
			ImagePlus channelToBeAnalyzed = new ImagePlus("CurrentChannel", stack);

			rt_nuclearML = new ResultsTable();
			RoiManager rm_nuclear = new RoiManager();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclearML = rm_nuclear.multiMeasure(channelToBeAnalyzed);
			rm_nuclear.close();
			Analyzer.setMeasurements(initialMeasurements);
			rt_nuclearML_flag = true;
		}

		int nbObjects=0;
		int[] nbObjectsPerClass = new int[numOfClasses];
		for(int i=0;i<numOfClasses;i++) {
			nbObjectsPerClass[i] = objectsInEachClass[i].size();
			nbObjects += nbObjectsPerClass[i];
		}
		double[][] currentFeatures = new double[nbObjects][nbFeatures-1];
		double[] avgCurrentFeatures = new double[nbFeatures-1],
				minCurrentFeatures = new double[nbFeatures-1],
				maxCurrentFeatures = new double[nbFeatures-1];
		for(int i=0;i<(nbFeatures-1);i++){
			avgCurrentFeatures[i] = 0;
			minCurrentFeatures[i] = 10000;
			maxCurrentFeatures[i] = 0;
		}

		nbObjects=0;
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				double avgValue = 0, stdValue = 0;
				Polygon fp = cellComponentInEachClass[i].get(j);
				for(int p=0;p<fp.npoints;p++) {
					avgValue += ipt.getf(fp.xpoints[p],fp.ypoints[p]);
				}
				avgValue /= (float)fp.npoints;
				for(int p=0;p<fp.npoints;p++) {
					stdValue += Math.pow(((double)ipt.getf(fp.xpoints[p],fp.ypoints[p])-avgValue), (double)2);
				}
				stdValue /= (float)fp.npoints;
				if (Double.isNaN(avgValue)) {
					currentFeatures[nbObjects][0] = 0;
				}
				else{
					currentFeatures[nbObjects][0] = avgValue;
				}
				if (Double.isNaN(stdValue)) {
					currentFeatures[nbObjects][1] = 0;
				}
				else{
					currentFeatures[nbObjects][1] = stdValue;
				}
				if (Double.isNaN(avgValue)) {
					currentFeatures[nbObjects][2] = 0;
				}
				else{
					currentFeatures[nbObjects][2] = rt_nuclearML.getValueAsDouble(4*nbObjects, 0);
				}
				if (Double.isNaN(avgValue)) {
					currentFeatures[nbObjects][3] = 0;
				}
				else{
					currentFeatures[nbObjects][3] = (double)(objectsInEachClass[i].get(j).length);
				}
				avgCurrentFeatures[0] += currentFeatures[nbObjects][0];
				avgCurrentFeatures[1] += currentFeatures[nbObjects][1];
				avgCurrentFeatures[2] += currentFeatures[nbObjects][2];
				avgCurrentFeatures[3] += currentFeatures[nbObjects][3];
				if(currentFeatures[nbObjects][0]<minCurrentFeatures[0]){minCurrentFeatures[0] = currentFeatures[nbObjects][0];}
				if(currentFeatures[nbObjects][0]>maxCurrentFeatures[0]){maxCurrentFeatures[0] = currentFeatures[nbObjects][0];}
				if(currentFeatures[nbObjects][1]<minCurrentFeatures[1]){minCurrentFeatures[1] = currentFeatures[nbObjects][1];}
				if(currentFeatures[nbObjects][1]>maxCurrentFeatures[1]){maxCurrentFeatures[1] = currentFeatures[nbObjects][1];}
				if(currentFeatures[nbObjects][2]<minCurrentFeatures[2]){minCurrentFeatures[2] = currentFeatures[nbObjects][2];}
				if(currentFeatures[nbObjects][2]>maxCurrentFeatures[2]){maxCurrentFeatures[2] = currentFeatures[nbObjects][2];}
				if(currentFeatures[nbObjects][3]<minCurrentFeatures[3]){minCurrentFeatures[3] = currentFeatures[nbObjects][3];}
				if(currentFeatures[nbObjects][3]>maxCurrentFeatures[3]){maxCurrentFeatures[3] = currentFeatures[nbObjects][3];}
				nbObjects++;
			}
		}
		for(int i=0;i<(nbFeatures-1);i++){
			avgCurrentFeatures[i] /= (double)nbObjects;
		}
		nbObjects = 0;
		double[] currentFeaturesRange = new double[nbFeatures-1];
		for(int i=0;i<(nbFeatures-1);i++) {
			if((maxCurrentFeatures[i]-minCurrentFeatures[i])>0){currentFeaturesRange[i] = maxCurrentFeatures[i]-minCurrentFeatures[i];}
			else{currentFeaturesRange[i] = (double)1;}
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				currentFeatures[nbObjects][0] = (currentFeatures[nbObjects][0]-avgCurrentFeatures[0])/currentFeaturesRange[0];
				currentFeatures[nbObjects][1] = (currentFeatures[nbObjects][1]-avgCurrentFeatures[1])/currentFeaturesRange[1];
				currentFeatures[nbObjects][2] = (currentFeatures[nbObjects][2]-avgCurrentFeatures[2])/currentFeaturesRange[2];
				currentFeatures[nbObjects][3] = (currentFeatures[nbObjects][3]-avgCurrentFeatures[3])/currentFeaturesRange[3];
				mc.addTestingDatasetElement(currentFeatures[nbObjects][0],currentFeatures[nbObjects][1],currentFeatures[nbObjects][2],currentFeatures[nbObjects][3]);
				nbObjects++;
			}
		}
		// create training dataset
		// positively labeled
		mc.initializeTrainingDataset();
		for(int i=0;i<positivelyLabelledNucleiForEachMarker[markerToBeProcessed].size();i++){
			Point[] pts = overlay.get(positivelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].get(i)).getContainedPoints();
			int currentX=-1,currentY=-1;
			if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
				currentX = pts[pts.length/2].x;
				currentY = pts[pts.length/2].y;
			}
			else {
				for(int k = 0; k < pts.length; k++) {
					if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
						currentX = pts[k].x;
						currentY = pts[k].y;
					}
				}
			}
			if(currentX>(-1)) {
				if((roiFlag[currentX][currentY][0]>(-1))&&(roiFlag[currentX][currentY][1]>(-1))) {
					int currentIndex=0;
					for(int p=0;p<roiFlag[currentX][currentY][0];p++){
						currentIndex += nbObjectsPerClass[p];
					}
					currentIndex += roiFlag[currentX][currentY][1];
					mc.addTrainingDatasetElement(currentFeatures[currentIndex][0], currentFeatures[currentIndex][1], currentFeatures[currentIndex][2], currentFeatures[currentIndex][3], 0);
				}
			}
		}
		// negatively labelled
		for(int i=0;i<negativelyLabelledNucleiForEachMarker[markerToBeProcessed].size();i++){
			Point[] pts = overlay.get(negativelyLabelledNucleiForEachMarker[currentObjectAssociatedMarker].get(i)).getContainedPoints();
			int currentX=-1,currentY=-1;
			if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
				currentX = pts[pts.length/2].x;
				currentY = pts[pts.length/2].y;
			}
			else {
				for(int k = 0; k < pts.length; k++) {
					if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
						currentX = pts[k].x;
						currentY = pts[k].y;
					}
				}
			}
			if(currentX>(-1)) {
				if((roiFlag[currentX][currentY][0]>(-1))&&(roiFlag[currentX][currentY][1]>(-1))) {
					int currentIndex=0;
					for(int p=0;p<roiFlag[currentX][currentY][0];p++){
						currentIndex += nbObjectsPerClass[p];
					}
					currentIndex += roiFlag[currentX][currentY][1];
					mc.addTrainingDatasetElement(currentFeatures[currentIndex][0], currentFeatures[currentIndex][1], currentFeatures[currentIndex][2], currentFeatures[currentIndex][3], 1);
				}
			}
			
		}
		// add stored features to training dataset
		if(featuresForEachMarker[markerToBeProcessed].size()>0){
			for(int i=0;i<featuresForEachMarker[markerToBeProcessed].size();i++){
				double[] previousFeatures = featuresForEachMarker[markerToBeProcessed].get(i);
				mc.addTrainingDatasetElement(previousFeatures[0],previousFeatures[1],previousFeatures[2],previousFeatures[3],previousFeatures[4]);
			}
		}

		// show training dataset
		//mc.showTrainingDataset();
		// train classifier
		try {
			mc.train();
		} 
		catch (InterruptedException ie)
		{
			IJ.log("Classifier construction was interrupted.");
			return;
		}
		catch(Exception e){
			IJ.showMessage("Training exception: " + e.getMessage());
			e.printStackTrace();
			return;
		}

		// processing all nuclei
		boolean[] positiveCells;
		try {
			positiveCells = mc.test();
		} 
		catch (InterruptedException ie)
		{
			IJ.log("Test was interrupted.");
			return;
		}
		catch(Exception e){
			IJ.showMessage("Test exception: " + e.getMessage());
			e.printStackTrace();
			return;
		}

		// annotate nuclei
		int index= 0 ;
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				if(positiveCells[index]==true){
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					activateNucleusMarkerML(currentNucleus[currentNucleus.length/2]);
				}
				index++;
			}
		}
		activateCurrentNucleiMarkerOverlays(markerToBeProcessed);
	}
	/**
	 * Train classifier to estimate markers associated objects and process
	 */
	void storeFeaturesForTraining(){
		for(int markerToBeProcessed=0;markerToBeProcessed<MAX_NUM_MARKERS;markerToBeProcessed++){
			if(methodToIdentifyObjectAssociatedMarkers[markerToBeProcessed]==2){
				// extract cell component needed for current marker
				List<Polygon> [] cellComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellComponentInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellComponentInEachClass[i].add(fp);
					}
				}
				if(markerCellcompartment[markerToBeProcessed]==0) {
					if(!nuclearComponentFlag){
						computeNuclearComponent();
						nuclearComponentFlag = true;
					}
					for(int i=0;i<numOfClasses;i++) {
						for(int y=0;y<displayImage.getHeight();y++) {
							for(int x=0;x<displayImage.getWidth();x++) {
								if(nuclearComponent[i][x][y]>0) {
									cellComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
								}
							}
						}
					}
				}
				else if(markerCellcompartment[markerToBeProcessed]==1) {
					if(!nuclearComponentFlag){
						computeNuclearComponent();
						nuclearComponentFlag = true;
					}
					if(!innerNuclearComponentFlag){
						computeInnerNuclearComponent();
						innerNuclearComponentFlag = true;
					}
					if(!membranarComponentFlag){
						computeMembranarComponent();
						membranarComponentFlag = true;
					}
					for(int i=0;i<numOfClasses;i++) {
						for(int y=0;y<displayImage.getHeight();y++) {
							for(int x=0;x<displayImage.getWidth();x++) {
								if(membranarComponent[i][x][y]>0) {
									cellComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
								}
							}
						}
					}
				}
				else if(markerCellcompartment[markerToBeProcessed]==2) {
					if(!nuclearComponentFlag){
						computeNuclearComponent();
						nuclearComponentFlag = true;
					}
					if(!innerNuclearComponentFlag){
						computeInnerNuclearComponent();
						innerNuclearComponentFlag = true;
					}
					if(!cytoplasmicComponentFlag){
						computeCytoplasmicComponent();
						cytoplasmicComponentFlag = true;
					}
					for(int i=0;i<numOfClasses;i++) {
						for(int y=0;y<displayImage.getHeight();y++) {
							for(int x=0;x<displayImage.getWidth();x++) {
								if(cytoplasmicComponent[i][x][y]>0) {
									cellComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
								}
							}
						}
					}
				}
				// get channel
				ImageProcessor ipt = displayImage.getStack().getProcessor(channelsForObjectAssociatedMarkers[markerToBeProcessed]);
				if(!rt_nuclearML_flag){
					int initialMeasurements = Analyzer.getMeasurements(),
							measurementsForFeatures = Measurements.CIRCULARITY;
					Analyzer.setMeasurements(measurementsForFeatures);

					ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
					stack.addSlice(ipt);
					ImagePlus channelToBeAnalyzed = new ImagePlus("CurrentChannel", stack);
					rt_nuclearML = new ResultsTable();
					RoiManager rm_nuclear = new RoiManager();
					for(int i=0;i<numOfClasses;i++) {
						for(int j=0;j<objectsInEachClass[i].size();j++) {
							Point[] currentNucleus = objectsInEachClass[i].get(j);
							int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
							for(int p=0;p<xPts.length;p++) {
								xPts[p] = currentNucleus[p].x;
								yPts[p] = currentNucleus[p].y;
							}
							PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
							ShapeRoi sr = new ShapeRoi(pr);
							rm_nuclear.addRoi(sr);
						}
					}
					rt_nuclearML = rm_nuclear.multiMeasure(channelToBeAnalyzed);
					rm_nuclear.close();
					Analyzer.setMeasurements(initialMeasurements);
					rt_nuclearML_flag = true;
				}
				int nbObjects=0;
				int[] nbObjectsPerClass = new int[numOfClasses];
				for(int i=0;i<numOfClasses;i++) {
					nbObjectsPerClass[i] = objectsInEachClass[i].size();
					nbObjects += nbObjectsPerClass[i];
				}
				double[][] currentFeatures = new double[nbObjects][nbFeatures-1];
				double[] avgCurrentFeatures = new double[nbFeatures-1],
						minCurrentFeatures = new double[nbFeatures-1],
						maxCurrentFeatures = new double[nbFeatures-1];
				for(int i=0;i<(nbFeatures-1);i++){
					avgCurrentFeatures[i] = 0;
					minCurrentFeatures[i] = 10000;
					maxCurrentFeatures[i] = 0;
				}
				nbObjects=0;
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						double avgValue = 0, stdValue = 0;
						Polygon fp = cellComponentInEachClass[i].get(j);
						for(int p=0;p<fp.npoints;p++) {
							avgValue += ipt.getf(fp.xpoints[p],fp.ypoints[p]);
						}
						avgValue /= (float)fp.npoints;
						for(int p=0;p<fp.npoints;p++) {
							stdValue += Math.pow(((double)ipt.getf(fp.xpoints[p],fp.ypoints[p])-avgValue), (double)2);
						}
						stdValue /= (float)fp.npoints;
						if (Double.isNaN(avgValue)) {
							currentFeatures[nbObjects][0] = 0;
						}
						else{
							currentFeatures[nbObjects][0] = avgValue;
						}
						if (Double.isNaN(stdValue)) {
							currentFeatures[nbObjects][1] = 0;
						}
						else{
							currentFeatures[nbObjects][1] = stdValue;
						}
						if (Double.isNaN(avgValue)) {
							currentFeatures[nbObjects][2] = 0;
						}
						else{
							currentFeatures[nbObjects][2] = rt_nuclearML.getValueAsDouble(4*nbObjects, 0);
						}
						if (Double.isNaN(avgValue)) {
							currentFeatures[nbObjects][3] = 0;
						}
						else{
							currentFeatures[nbObjects][3] = (double)(objectsInEachClass[i].get(j).length);
						}
						avgCurrentFeatures[0] += currentFeatures[nbObjects][0];
						avgCurrentFeatures[1] += currentFeatures[nbObjects][1];
						avgCurrentFeatures[2] += currentFeatures[nbObjects][2];
						avgCurrentFeatures[3] += currentFeatures[nbObjects][3];
						if(currentFeatures[nbObjects][0]<minCurrentFeatures[0]){minCurrentFeatures[0] = currentFeatures[nbObjects][0];}
						if(currentFeatures[nbObjects][0]>maxCurrentFeatures[0]){maxCurrentFeatures[0] = currentFeatures[nbObjects][0];}
						if(currentFeatures[nbObjects][1]<minCurrentFeatures[1]){minCurrentFeatures[1] = currentFeatures[nbObjects][1];}
						if(currentFeatures[nbObjects][1]>maxCurrentFeatures[1]){maxCurrentFeatures[1] = currentFeatures[nbObjects][1];}
						if(currentFeatures[nbObjects][2]<minCurrentFeatures[2]){minCurrentFeatures[2] = currentFeatures[nbObjects][2];}
						if(currentFeatures[nbObjects][2]>maxCurrentFeatures[2]){maxCurrentFeatures[2] = currentFeatures[nbObjects][2];}
						if(currentFeatures[nbObjects][3]<minCurrentFeatures[3]){minCurrentFeatures[3] = currentFeatures[nbObjects][3];}
						if(currentFeatures[nbObjects][3]>maxCurrentFeatures[3]){maxCurrentFeatures[3] = currentFeatures[nbObjects][3];}
						nbObjects++;
					}
				}
				for(int i=0;i<(nbFeatures-1);i++){
					avgCurrentFeatures[i] /= (double)nbObjects;
				}
				nbObjects = 0;
				double[] currentFeaturesRange = new double[nbFeatures-1];
				for(int i=0;i<(nbFeatures-1);i++) {
					if((maxCurrentFeatures[i]-minCurrentFeatures[i])>0){currentFeaturesRange[i] = maxCurrentFeatures[i]-minCurrentFeatures[i];}
					else{currentFeaturesRange[i] = (double)1;}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						currentFeatures[nbObjects][0] = (currentFeatures[nbObjects][0]-avgCurrentFeatures[0])/currentFeaturesRange[0];
						currentFeatures[nbObjects][1] = (currentFeatures[nbObjects][1]-avgCurrentFeatures[1])/currentFeaturesRange[1];
						currentFeatures[nbObjects][2] = (currentFeatures[nbObjects][2]-avgCurrentFeatures[2])/currentFeaturesRange[2];
						currentFeatures[nbObjects][3] = (currentFeatures[nbObjects][3]-avgCurrentFeatures[3])/currentFeaturesRange[3];
						nbObjects++;
					}
				}
				// positively labeled
				for(int i=0;i<positivelyLabelledNucleiForEachMarker[markerToBeProcessed].size();i++){
					Point[] pts = overlay.get(positivelyLabelledNucleiForEachMarker[markerToBeProcessed].get(i)).getContainedPoints();
					int currentX=-1,currentY=-1;
					if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
						currentX = pts[pts.length/2].x;
						currentY = pts[pts.length/2].y;
					}
					else {
						for(int k = 0; k < pts.length; k++) {
							if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
								currentX = pts[k].x;
								currentY = pts[k].y;
							}
						}
					}
					if(currentX>(-1)) {
						if((roiFlag[currentX][currentY][0]>(-1))&&(roiFlag[currentX][currentY][1]>(-1))) {
							int currentIndex=0;
							for(int p=0;p<roiFlag[currentX][currentY][0];p++){
								currentIndex += nbObjectsPerClass[p];
							}
							currentIndex += roiFlag[currentX][currentY][1];
							double[] features = new double[nbFeatures];
							for(int p=0;p<(nbFeatures-1);p++){
								features[p] = currentFeatures[currentIndex][p];
							}							
							features[nbFeatures-1] = 0;
							featuresForEachMarker[markerToBeProcessed].add(features);
						}
					}
				}
				// negatively labelled
				for(int i=0;i<negativelyLabelledNucleiForEachMarker[markerToBeProcessed].size();i++){
					Point[] pts = overlay.get(negativelyLabelledNucleiForEachMarker[markerToBeProcessed].get(i)).getContainedPoints();
					int currentX=-1,currentY=-1;
					if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
						currentX = pts[pts.length/2].x;
						currentY = pts[pts.length/2].y;
					}
					else {
						for(int k = 0; k < pts.length; k++) {
							if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
								currentX = pts[k].x;
								currentY = pts[k].y;
							}
						}
					}
					if(currentX>(-1)) {
						if((roiFlag[currentX][currentY][0]>(-1))&&(roiFlag[currentX][currentY][1]>(-1))) {
							int currentIndex=0;
							for(int p=0;p<roiFlag[currentX][currentY][0];p++){
								currentIndex += nbObjectsPerClass[p];
							}
							currentIndex += roiFlag[currentX][currentY][1];
							double[] features = new double[nbFeatures];
							for(int p=0;p<(nbFeatures-1);p++){
								features[p] = currentFeatures[currentIndex][p];
							}							
							features[nbFeatures-1] = 1;
							featuresForEachMarker[markerToBeProcessed].add(features);
						}
					}
					
				}
			}
		}
	}
	/**
	 * extract data for a given classifier
	 */
	ArrayList<double[]> featuresToBeSaved(int markerToBeProcessed){
		ArrayList<double[]> output = new ArrayList<double[]>();
		
		// extract cell component needed for current marker
		List<Polygon> [] cellComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];
		for(int i=0;i<numOfClasses;i++) {
			cellComponentInEachClass[i] = new ArrayList<Polygon>();
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				Polygon fp = new Polygon();
				cellComponentInEachClass[i].add(fp);
			}
		}
		if(markerCellcompartment[markerToBeProcessed]==0) {
			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(nuclearComponent[i][x][y]>0) {
							cellComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
						}
					}
				}
			}
		}
		else if(markerCellcompartment[markerToBeProcessed]==1) {
			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			if(!innerNuclearComponentFlag){
				computeInnerNuclearComponent();
				innerNuclearComponentFlag = true;
			}
			if(!membranarComponentFlag){
				computeMembranarComponent();
				membranarComponentFlag = true;
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(membranarComponent[i][x][y]>0) {
							cellComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
						}
					}
				}
			}
		}
		else if(markerCellcompartment[markerToBeProcessed]==2) {
			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			if(!innerNuclearComponentFlag){
				computeInnerNuclearComponent();
				innerNuclearComponentFlag = true;
			}
			if(!cytoplasmicComponentFlag){
				computeCytoplasmicComponent();
				cytoplasmicComponentFlag = true;
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(cytoplasmicComponent[i][x][y]>0) {
							cellComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
						}
					}
				}
			}
		}
		// get channel
		ImageProcessor ipt = displayImage.getStack().getProcessor(channelsForObjectAssociatedMarkers[markerToBeProcessed]);
		if(!rt_nuclearML_flag){
			int initialMeasurements = Analyzer.getMeasurements(),
					measurementsForFeatures = Measurements.CIRCULARITY;
			Analyzer.setMeasurements(measurementsForFeatures);

			ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
			stack.addSlice(ipt);
			ImagePlus channelToBeAnalyzed = new ImagePlus("CurrentChannel", stack);
			rt_nuclearML = new ResultsTable();
			RoiManager rm_nuclear = new RoiManager();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclearML = rm_nuclear.multiMeasure(channelToBeAnalyzed);
			rm_nuclear.close();
			Analyzer.setMeasurements(initialMeasurements);
			rt_nuclearML_flag = true;
		}
		int nbObjects=0;
		int[] nbObjectsPerClass = new int[numOfClasses];
		for(int i=0;i<numOfClasses;i++) {
			nbObjectsPerClass[i] = objectsInEachClass[i].size();
			nbObjects += nbObjectsPerClass[i];
		}
		double[][] currentFeatures = new double[nbObjects][nbFeatures-1];
		double[] avgCurrentFeatures = new double[nbFeatures-1],
				minCurrentFeatures = new double[nbFeatures-1],
				maxCurrentFeatures = new double[nbFeatures-1];
		for(int i=0;i<(nbFeatures-1);i++){
			avgCurrentFeatures[i] = 0;
			minCurrentFeatures[i] = 10000;
			maxCurrentFeatures[i] = 0;
		}
		nbObjects=0;
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				double avgValue = 0, stdValue = 0;
				Polygon fp = cellComponentInEachClass[i].get(j);
				for(int p=0;p<fp.npoints;p++) {
					avgValue += ipt.getf(fp.xpoints[p],fp.ypoints[p]);
				}
				avgValue /= (float)fp.npoints;
				for(int p=0;p<fp.npoints;p++) {
					stdValue += Math.pow(((double)ipt.getf(fp.xpoints[p],fp.ypoints[p])-avgValue), (double)2);
				}
				stdValue /= (float)fp.npoints;
				if (Double.isNaN(avgValue)) {
					currentFeatures[nbObjects][0] = 0;
				}
				else{
					currentFeatures[nbObjects][0] = avgValue;
				}
				if (Double.isNaN(stdValue)) {
					currentFeatures[nbObjects][1] = 0;
				}
				else{
					currentFeatures[nbObjects][1] = stdValue;
				}
				if (Double.isNaN(avgValue)) {
					currentFeatures[nbObjects][2] = 0;
				}
				else{
					currentFeatures[nbObjects][2] = rt_nuclearML.getValueAsDouble(4*nbObjects, 0);
				}
				if (Double.isNaN(avgValue)) {
					currentFeatures[nbObjects][3] = 0;
				}
				else{
					currentFeatures[nbObjects][3] = (double)(objectsInEachClass[i].get(j).length);
				}
				avgCurrentFeatures[0] += currentFeatures[nbObjects][0];
				avgCurrentFeatures[1] += currentFeatures[nbObjects][1];
				avgCurrentFeatures[2] += currentFeatures[nbObjects][2];
				avgCurrentFeatures[3] += currentFeatures[nbObjects][3];
				if(currentFeatures[nbObjects][0]<minCurrentFeatures[0]){minCurrentFeatures[0] = currentFeatures[nbObjects][0];}
				if(currentFeatures[nbObjects][0]>maxCurrentFeatures[0]){maxCurrentFeatures[0] = currentFeatures[nbObjects][0];}
				if(currentFeatures[nbObjects][1]<minCurrentFeatures[1]){minCurrentFeatures[1] = currentFeatures[nbObjects][1];}
				if(currentFeatures[nbObjects][1]>maxCurrentFeatures[1]){maxCurrentFeatures[1] = currentFeatures[nbObjects][1];}
				if(currentFeatures[nbObjects][2]<minCurrentFeatures[2]){minCurrentFeatures[2] = currentFeatures[nbObjects][2];}
				if(currentFeatures[nbObjects][2]>maxCurrentFeatures[2]){maxCurrentFeatures[2] = currentFeatures[nbObjects][2];}
				if(currentFeatures[nbObjects][3]<minCurrentFeatures[3]){minCurrentFeatures[3] = currentFeatures[nbObjects][3];}
				if(currentFeatures[nbObjects][3]>maxCurrentFeatures[3]){maxCurrentFeatures[3] = currentFeatures[nbObjects][3];}
				nbObjects++;
			}
		}
		for(int i=0;i<(nbFeatures-1);i++){
			avgCurrentFeatures[i] /= (double)nbObjects;
		}
		nbObjects = 0;
		double[] currentFeaturesRange = new double[nbFeatures-1];
		for(int i=0;i<(nbFeatures-1);i++) {
			if((maxCurrentFeatures[i]-minCurrentFeatures[i])>0){currentFeaturesRange[i] = maxCurrentFeatures[i]-minCurrentFeatures[i];}
			else{currentFeaturesRange[i] = (double)1;}
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				currentFeatures[nbObjects][0] = (currentFeatures[nbObjects][0]-avgCurrentFeatures[0])/currentFeaturesRange[0];
				currentFeatures[nbObjects][1] = (currentFeatures[nbObjects][1]-avgCurrentFeatures[1])/currentFeaturesRange[1];
				currentFeatures[nbObjects][2] = (currentFeatures[nbObjects][2]-avgCurrentFeatures[2])/currentFeaturesRange[2];
				currentFeatures[nbObjects][3] = (currentFeatures[nbObjects][3]-avgCurrentFeatures[3])/currentFeaturesRange[3];
				nbObjects++;
			}
		}
		// positively labeled
		for(int i=0;i<positivelyLabelledNucleiForEachMarker[markerToBeProcessed].size();i++){
			Point[] pts = overlay.get(positivelyLabelledNucleiForEachMarker[markerToBeProcessed].get(i)).getContainedPoints();
			int currentX=-1,currentY=-1;
			if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
				currentX = pts[pts.length/2].x;
				currentY = pts[pts.length/2].y;
			}
			else {
				for(int k = 0; k < pts.length; k++) {
					if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
						currentX = pts[k].x;
						currentY = pts[k].y;
					}
				}
			}
			if(currentX>(-1)) {
				if((roiFlag[currentX][currentY][0]>(-1))&&(roiFlag[currentX][currentY][1]>(-1))) {
					int currentIndex=0;
					for(int p=0;p<roiFlag[currentX][currentY][0];p++){
						currentIndex += nbObjectsPerClass[p];
					}
					currentIndex += roiFlag[currentX][currentY][1];
					double[] features = new double[nbFeatures];
					for(int p=0;p<(nbFeatures-1);p++){
						features[p] = currentFeatures[currentIndex][p];
					}							
					features[nbFeatures-1] = 0;
					output.add(features);
				}
			}
		}
		// negatively labelled
		for(int i=0;i<negativelyLabelledNucleiForEachMarker[markerToBeProcessed].size();i++){
			Point[] pts = overlay.get(negativelyLabelledNucleiForEachMarker[markerToBeProcessed].get(i)).getContainedPoints();
			int currentX=-1,currentY=-1;
			if(roiFlag[pts[pts.length/2].x][pts[pts.length/2].y][2]>(-1)) {
				currentX = pts[pts.length/2].x;
				currentY = pts[pts.length/2].y;
			}
			else {
				for(int k = 0; k < pts.length; k++) {
					if(roiFlag[pts[k].x][pts[k].y][2]>(-1)) {
						currentX = pts[k].x;
						currentY = pts[k].y;
					}
				}
			}
			if(currentX>(-1)) {
				if((roiFlag[currentX][currentY][0]>(-1))&&(roiFlag[currentX][currentY][1]>(-1))) {
					int currentIndex=0;
					for(int p=0;p<roiFlag[currentX][currentY][0];p++){
						currentIndex += nbObjectsPerClass[p];
					}
					currentIndex += roiFlag[currentX][currentY][1];
					double[] features = new double[nbFeatures];
					for(int p=0;p<(nbFeatures-1);p++){
						features[p] = currentFeatures[currentIndex][p];
					}							
					features[nbFeatures-1] = 1;
					output.add(features);
				}
			}
		}
		return output;
	}
	/**
	 * Summarize all info
	 */
	private void classesMeasurements() 
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			RoiManager rm_nuclear = new RoiManager();
			ResultsTable rt_nuclear = new ResultsTable(), rt_membranar = new ResultsTable(), rt_cytoplasmic = new ResultsTable(), rt_cell = new ResultsTable();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclear = rm_nuclear.multiMeasure(displayImage);
			rm_nuclear.close();

			if(membranarComponentFlag){
				RoiManager rm_membranar = new RoiManager();
				List<Polygon> [] nuclearMembranesInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					nuclearMembranesInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						nuclearMembranesInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								nuclearMembranesInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = nuclearMembranesInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_membranar.addRoi(sr);
					}
				}
				rt_membranar = rm_membranar.multiMeasure(displayImage);
				rm_membranar.close();
			}

			if(cytoplasmicComponentFlag){
				RoiManager rm_cytoplasmic = new RoiManager();
				List<Polygon> [] cytoplasmicInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cytoplasmicInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cytoplasmicInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cytoplasmicInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cytoplasmic.addRoi(sr);
					}
				}
				rt_cytoplasmic = rm_cytoplasmic.multiMeasure(displayImage);
				rm_cytoplasmic.close();
			}

			if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
				int[][][] cellComponent = computeCellComponent();
				RoiManager rm_cell = new RoiManager();
				List<Polygon> [] cellsInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellsInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellsInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cellComponent[i][x][y]>0) {
								cellsInEachClass[i].get(cellComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}

				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cellsInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cell.addRoi(sr);
					}
				}
				rt_cell = rm_cell.multiMeasure(displayImage);
				rm_cell.close();
			}

			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}

			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt_nuclear.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt_nuclear.getValueAsDouble(k, 0), value2 = rt_nuclear.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			int rtIndex=0;
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					finalRt.incrementCounter();
					for(int k=0;k<nbFeatures;k++) {
						if(intensityFeatures[k]==0) {
							finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1), rt_nuclear.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear component", rt_nuclear.getValueAsDouble(rtIndex, c));
							}
							if(membranarComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_membranar.getColumnHeading(k).substring(0, rt_membranar.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear membrane component", rt_membranar.getValueAsDouble(rtIndex, c));
								}}
							if(cytoplasmicComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cytoplasmic.getColumnHeading(k).substring(0, rt_cytoplasmic.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cytoplasmic component", rt_cytoplasmic.getValueAsDouble(rtIndex, c));
								}}
							if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cell.getColumnHeading(k).substring(0, rt_cell.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cell component", rt_cell.getValueAsDouble(rtIndex, c));
								}}
							rtIndex++;
						}
					}
					if(numOfClasses>1){
						finalRt.addValue("Object class", i+1);
					}
					if((areasInEachClass[0].size()>0)||(numOfAreas>1)){
						Point[] pl = objectsInEachClass[i].get(j);
						boolean areaBool=false;

						if(areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]>(-1)){
							finalRt.addValue("Region class", areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]+1);
							areaBool = true;
						}
						if(!areaBool){
							finalRt.addValue("Region class", 0);
						}
					}
				}
			}
			finalRt.show("Results");
		}
	}
	private void classesMeasurements(String outputPath) 
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			RoiManager rm_nuclear = new RoiManager();
			ResultsTable rt_nuclear = new ResultsTable(), rt_membranar = new ResultsTable(), rt_cytoplasmic = new ResultsTable(), rt_cell = new ResultsTable();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclear = rm_nuclear.multiMeasure(displayImage);
			rm_nuclear.close();

			if(membranarComponentFlag){
				RoiManager rm_membranar = new RoiManager();
				List<Polygon> [] nuclearMembranesInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					nuclearMembranesInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						nuclearMembranesInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								nuclearMembranesInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = nuclearMembranesInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_membranar.addRoi(sr);
					}
				}
				rt_membranar = rm_membranar.multiMeasure(displayImage);
				rm_membranar.close();
			}

			if(cytoplasmicComponentFlag){
				RoiManager rm_cytoplasmic = new RoiManager();
				List<Polygon> [] cytoplasmicInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cytoplasmicInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cytoplasmicInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cytoplasmicInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cytoplasmic.addRoi(sr);
					}
				}
				rt_cytoplasmic = rm_cytoplasmic.multiMeasure(displayImage);
				rm_cytoplasmic.close();
			}

			if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
				int[][][] cellComponent = computeCellComponent();
				RoiManager rm_cell = new RoiManager();
				List<Polygon> [] cellsInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellsInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellsInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cellComponent[i][x][y]>0) {
								cellsInEachClass[i].get(cellComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}

				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cellsInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cell.addRoi(sr);
					}
				}
				rt_cell = rm_cell.multiMeasure(displayImage);
				rm_cell.close();
			}

			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}

			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt_nuclear.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt_nuclear.getValueAsDouble(k, 0), value2 = rt_nuclear.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			int rtIndex=0;
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					finalRt.incrementCounter();
					for(int k=0;k<nbFeatures;k++) {
						if(intensityFeatures[k]==0) {
							finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1), rt_nuclear.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear component", rt_nuclear.getValueAsDouble(rtIndex, c));
							}
							if(membranarComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_membranar.getColumnHeading(k).substring(0, rt_membranar.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear membrane component", rt_membranar.getValueAsDouble(rtIndex, c));
								}}
							if(cytoplasmicComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cytoplasmic.getColumnHeading(k).substring(0, rt_cytoplasmic.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cytoplasmic component", rt_cytoplasmic.getValueAsDouble(rtIndex, c));
								}}
							if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cell.getColumnHeading(k).substring(0, rt_cell.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cell component", rt_cell.getValueAsDouble(rtIndex, c));
								}}
							rtIndex++;
						}
					}
					if(numOfClasses>1){
						finalRt.addValue("Object class", i+1);
					}
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];

					if((areasInEachClass[0].size()>0)||(numOfAreas>1)){
						boolean areaBool=false;
						if(areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]>(-1)){
							finalRt.addValue("Region class", areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]+1);
							areaBool = true;
						}
						if(!areaBool){
							finalRt.addValue("Region class", 0);
						}
					}
				}
			}
			finalRt.save(outputPath);
		}
	}

	/**
	 * Summarize all info
	 */
	private void markerMeasurements() 
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			RoiManager rm_nuclear = new RoiManager();
			ResultsTable rt_nuclear = new ResultsTable(), rt_membranar = new ResultsTable(), rt_cytoplasmic = new ResultsTable(), rt_cell = new ResultsTable();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclear = rm_nuclear.multiMeasure(displayImage);
			rm_nuclear.close();

			if(membranarComponentFlag){
				RoiManager rm_membranar = new RoiManager();
				List<Polygon> [] nuclearMembranesInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					nuclearMembranesInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						nuclearMembranesInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								nuclearMembranesInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = nuclearMembranesInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_membranar.addRoi(sr);
					}
				}
				rt_membranar = rm_membranar.multiMeasure(displayImage);
				rm_membranar.close();
			}

			if(cytoplasmicComponentFlag){
				RoiManager rm_cytoplasmic = new RoiManager();
				List<Polygon> [] cytoplasmicInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cytoplasmicInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cytoplasmicInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cytoplasmicInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cytoplasmic.addRoi(sr);
					}
				}
				rt_cytoplasmic = rm_cytoplasmic.multiMeasure(displayImage);
				rm_cytoplasmic.close();
			}

			if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
				int[][][] cellComponent = computeCellComponent();
				RoiManager rm_cell = new RoiManager();
				List<Polygon> [] cellsInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellsInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellsInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cellComponent[i][x][y]>0) {
								cellsInEachClass[i].get(cellComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}

				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cellsInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cell.addRoi(sr);
					}
				}
				rt_cell = rm_cell.multiMeasure(displayImage);
				rm_cell.close();
			}

			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}
			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt_nuclear.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt_nuclear.getValueAsDouble(k, 0), value2 = rt_nuclear.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			int rtIndex=0;
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					finalRt.incrementCounter();
					for(int k=0;k<nbFeatures;k++) {
						if(intensityFeatures[k]==0) {
							finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1), rt_nuclear.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear component", rt_nuclear.getValueAsDouble(rtIndex, c));
							}
							if(membranarComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_membranar.getColumnHeading(k).substring(0, rt_membranar.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear membrane component", rt_membranar.getValueAsDouble(rtIndex, c));
								}}
							if(cytoplasmicComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cytoplasmic.getColumnHeading(k).substring(0, rt_cytoplasmic.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cytoplasmic component", rt_cytoplasmic.getValueAsDouble(rtIndex, c));
								}}
							if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cell.getColumnHeading(k).substring(0, rt_cell.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cell component", rt_cell.getValueAsDouble(rtIndex, c));
								}}
							rtIndex++;
						}
					}
					// object class
					if(numOfClasses>1){
						finalRt.addValue("Object class", i+1);
					}
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];

					// area class
					if((areasInEachClass[0].size()>0)||(numOfAreas>1)){
						boolean areaBool=false;
						if(areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]>(-1)){
							finalRt.addValue("Region class", areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]+1);
							areaBool = true;
						}
						if(!areaBool){
							finalRt.addValue("Region class", 0);
						}
					}

					// object associated markers
					for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
						int pattern = 0;
						for(int p=0;p<4;p++) {
							for(int q = 0; q < positiveNucleiForEachMarker[k][p].size(); q++) {
								if(positiveNucleiForEachMarker[k][p].get(q)==overlayId){
									pattern = p+1;
								}
							}
						}
						finalRt.addValue("Marker "+(k+1), pattern);
					}
				}
			}
			finalRt.show("Results");
		}
	}
	private void markerMeasurements(String outputPath, int nbCombinations, String[] combinationNames, short[][] markerCombinations)
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			RoiManager rm_nuclear = new RoiManager();
			ResultsTable rt_nuclear = new ResultsTable(), rt_membranar = new ResultsTable(), rt_cytoplasmic = new ResultsTable(), rt_cell = new ResultsTable();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclear = rm_nuclear.multiMeasure(displayImage);
			rm_nuclear.close();


			if(membranarComponentFlag){
				RoiManager rm_membranar = new RoiManager();
				List<Polygon> [] nuclearMembranesInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					nuclearMembranesInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						nuclearMembranesInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								nuclearMembranesInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = nuclearMembranesInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_membranar.addRoi(sr);
					}
				}
				rt_membranar = rm_membranar.multiMeasure(displayImage);
				rm_membranar.close();
			}

			if(cytoplasmicComponentFlag){
				RoiManager rm_cytoplasmic = new RoiManager();
				List<Polygon> [] cytoplasmicInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cytoplasmicInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cytoplasmicInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cytoplasmicInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cytoplasmic.addRoi(sr);
					}
				}
				rt_cytoplasmic = rm_cytoplasmic.multiMeasure(displayImage);
				rm_cytoplasmic.close();
			}

			if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
				int[][][] cellComponent = computeCellComponent();
				RoiManager rm_cell = new RoiManager();
				List<Polygon> [] cellsInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellsInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellsInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cellComponent[i][x][y]>0) {
								cellsInEachClass[i].get(cellComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}

				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cellsInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cell.addRoi(sr);
					}
				}
				rt_cell = rm_cell.multiMeasure(displayImage);
				rm_cell.close();
			}

			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}

			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt_nuclear.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt_nuclear.getValueAsDouble(k, 0), value2 = rt_nuclear.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			int rtIndex=0;
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					finalRt.incrementCounter();
					for(int k=0;k<nbFeatures;k++) {
						if(intensityFeatures[k]==0) {
							finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1), rt_nuclear.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear component", rt_nuclear.getValueAsDouble(rtIndex, c));
							}
							if(membranarComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_membranar.getColumnHeading(k).substring(0, rt_membranar.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear membrane component", rt_membranar.getValueAsDouble(rtIndex, c));
								}}
							if(cytoplasmicComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cytoplasmic.getColumnHeading(k).substring(0, rt_cytoplasmic.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cytoplasmic component", rt_cytoplasmic.getValueAsDouble(rtIndex, c));
								}}
							if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cell.getColumnHeading(k).substring(0, rt_cell.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cell component", rt_cell.getValueAsDouble(rtIndex, c));
								}}
							rtIndex++;
						}
					}
					// object class
					if(numOfClasses>1){
						finalRt.addValue("Object class", i+1);
					}

					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];

					// area class
					if((areasInEachClass[0].size()>0)||(numOfAreas>1)){
						boolean areaBool=false;
						if(areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]>(-1)){
							finalRt.addValue("Region class", areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]+1);
							areaBool = true;
						}
						if(!areaBool){
							finalRt.addValue("Region class", 0);
						}
					}

					// object associated markers
					short[] currentMarkerCombination = new short[numOfObjectAssociatedMarkers];
					for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
						int pattern = 0;
						for(int p=0;p<4;p++) {
							for(int q = 0; q < positiveNucleiForEachMarker[k][p].size(); q++) {
								if(positiveNucleiForEachMarker[k][p].get(q)==overlayId){
									pattern = p+1;
								}
							}
						}
						finalRt.addValue("Object marker "+(k+1), pattern);
						if(pattern>0){currentMarkerCombination[k] = 1;}
					}
					for(int p=0;p<nbCombinations;p++){
						boolean currentCombination = true;
						for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
							if(currentMarkerCombination[k]!=markerCombinations[p][k]){currentCombination=false;}
						}
						if(currentCombination){
							finalRt.addValue(combinationNames[p], 1);
						}
						else{
							finalRt.addValue(combinationNames[p], 0);
						}
					}
				}
			}
			finalRt.save(outputPath);
		}
	}
	private void markerMeasurementsAndAllSnapshots(String outputTextPath, String outputImagePath, int nbCombinations, String[] combinationNames, short[][] markerCombinations)
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			initializeMarkerButtons();
			removeMarkersFromOverlay();
			currentObjectAssociatedMarker = -1;

			ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
			int[][] markers_mask = new int[displayImage.getWidth()][displayImage.getHeight()];

			int[] cellCompartments = new int[3];
			for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
				if(markerCellcompartment[k]==0){
					cellCompartments[0] = 1;
				}
				else if(markerCellcompartment[k]==1){
					cellCompartments[1] = 1;
				}
				else if(markerCellcompartment[k]==2){
					cellCompartments[2] = 1;
				}
			}

			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			if((cellCompartments[1]==1)||(cellCompartments[2]==1)){
				if(!innerNuclearComponentFlag){
					computeInnerNuclearComponent();
					innerNuclearComponentFlag = true;
				}
				if(cellCompartments[1]==1){
					if(!membranarComponentFlag){
						computeMembranarComponent();
						membranarComponentFlag = true;
					}
				}
				if(!cytoplasmicComponentFlag){
					computeCytoplasmicComponent();
					cytoplasmicComponentFlag = true;
				}
			}
			List<FloatPolygon> [] nuclearComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], membranarComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], cytoplasmicComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];

			for(int i=0;i<numOfClasses;i++) {
				if(cellCompartments[0]==1){nuclearComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
				if(cellCompartments[1]==1){membranarComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
				if(cellCompartments[2]==1){cytoplasmicComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					if(cellCompartments[0]==1){
						FloatPolygon fp1 = new FloatPolygon();
						nuclearComponentInEachClass[i].add(fp1);
					}
					if(cellCompartments[1]==1){
						FloatPolygon fp2 = new FloatPolygon();
						membranarComponentInEachClass[i].add(fp2);
					}
					if(cellCompartments[2]==1){
						FloatPolygon fp3 = new FloatPolygon();
						cytoplasmicComponentInEachClass[i].add(fp3);
					}
				}
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(cellCompartments[0]==1){
							if(nuclearComponent[i][x][y]>0) {
								nuclearComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
							}
						}
						if(cellCompartments[1]==1){
							if(membranarComponent[i][x][y]>0) {
								membranarComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
						if(cellCompartments[2]==1){
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
			}
			int[][] outputArray = new int[numOfObjectAssociatedMarkers][displayImage.getWidth()*displayImage.getHeight()];

			RoiManager rm_nuclear = new RoiManager();
			ResultsTable rt_nuclear = new ResultsTable(), rt_membranar = new ResultsTable(), rt_cytoplasmic = new ResultsTable(), rt_cell = new ResultsTable();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclear = rm_nuclear.multiMeasure(displayImage);
			rm_nuclear.close();

			if(membranarComponentFlag){
				RoiManager rm_membranar = new RoiManager();
				List<Polygon> [] nuclearMembranesInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					nuclearMembranesInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						nuclearMembranesInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								nuclearMembranesInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = nuclearMembranesInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_membranar.addRoi(sr);
					}
				}
				rt_membranar = rm_membranar.multiMeasure(displayImage);
				rm_membranar.close();
			}

			if(cytoplasmicComponentFlag){
				RoiManager rm_cytoplasmic = new RoiManager();
				List<Polygon> [] cytoplasmicInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cytoplasmicInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cytoplasmicInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cytoplasmicInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cytoplasmic.addRoi(sr);
					}
				}
				rt_cytoplasmic = rm_cytoplasmic.multiMeasure(displayImage);
				rm_cytoplasmic.close();
			}

			if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
				int[][][] cellComponent = computeCellComponent();
				RoiManager rm_cell = new RoiManager();
				List<Polygon> [] cellsInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellsInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellsInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cellComponent[i][x][y]>0) {
								cellsInEachClass[i].get(cellComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}

				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cellsInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cell.addRoi(sr);
					}
				}
				rt_cell = rm_cell.multiMeasure(displayImage);
				rm_cell.close();
			}

			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}

			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt_nuclear.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt_nuclear.getValueAsDouble(k, 0), value2 = rt_nuclear.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			int rtIndex=0;
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					finalRt.incrementCounter();
					for(int k=0;k<nbFeatures;k++) {
						if(intensityFeatures[k]==0) {
							finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1), rt_nuclear.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear component", rt_nuclear.getValueAsDouble(rtIndex, c));
							}
							if(membranarComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_membranar.getColumnHeading(k).substring(0, rt_membranar.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear membrane component", rt_membranar.getValueAsDouble(rtIndex, c));
								}}
							if(cytoplasmicComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cytoplasmic.getColumnHeading(k).substring(0, rt_cytoplasmic.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cytoplasmic component", rt_cytoplasmic.getValueAsDouble(rtIndex, c));
								}}
							if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cell.getColumnHeading(k).substring(0, rt_cell.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cell component", rt_cell.getValueAsDouble(rtIndex, c));
								}}
							rtIndex++;
						}
					}
					// object class
					if(numOfClasses>1){
						finalRt.addValue("Object class", i+1);
					}
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];
					// area class
					if((areasInEachClass[0].size()>0)||(numOfAreas>1)){
						boolean areaBool=false;
						if(areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]>(-1)){
							finalRt.addValue("Region class", areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]+1);
							areaBool = true;
						}
						if(!areaBool){
							finalRt.addValue("Region class", 0);
						}
					}
					// combination of markers
					short[] currentMarkerCombination = new short[numOfObjectAssociatedMarkers];
					for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
						int pattern = 0;
						for(int p=0;p<4;p++) {
							for(int q = 0; q < positiveNucleiForEachMarker[k][p].size(); q++) {
								if(positiveNucleiForEachMarker[k][p].get(q)==overlayId){
									pattern = p+1;
								}
							}
						}
						finalRt.addValue("Object marker "+(k+1), pattern);
						if(pattern>0){
							if(nbCombinations==0){
								if(markerCellcompartment[k]==0) {
									FloatPolygon fp = nuclearComponentInEachClass[i].get(j);
									for(int l=0;l<fp.npoints;l++) {
										outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
										markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
									}
								}
								else if(markerCellcompartment[k]==1) {
									FloatPolygon fp = membranarComponentInEachClass[i].get(j);
									for(int l=0;l<fp.npoints;l++) {
										outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
										markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
									}
								}
								else if(markerCellcompartment[k]==2) {
									FloatPolygon fp = cytoplasmicComponentInEachClass[i].get(j);
									for(int l=0;l<fp.npoints;l++) {
										outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
										markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
									}
								}							
							}
							else{
								currentMarkerCombination[k] = 1;
							}
						}
					}
					for(int p=0;p<nbCombinations;p++){
						boolean currentCombination = true;
						for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
							if(currentMarkerCombination[k]!=markerCombinations[p][k]){currentCombination=false;}
						}
						if(currentCombination){
							finalRt.addValue(combinationNames[p], 1);
							for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
								if(currentMarkerCombination[k]==1){
									if(markerCellcompartment[k]==0) {
										FloatPolygon fp = nuclearComponentInEachClass[i].get(j);
										for(int l=0;l<fp.npoints;l++) {
											outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
											markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
										}
									}
									else if(markerCellcompartment[k]==1) {
										FloatPolygon fp = membranarComponentInEachClass[i].get(j);
										for(int l=0;l<fp.npoints;l++) {
											outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
											markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
										}
									}
									else if(markerCellcompartment[k]==2) {
										FloatPolygon fp = cytoplasmicComponentInEachClass[i].get(j);
										for(int l=0;l<fp.npoints;l++) {
											outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
											markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
										}
									}
								}
							}
						}
						else{
							finalRt.addValue(combinationNames[p], 0);
						}
					}
				}
			}
			finalRt.save(outputTextPath);
			for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
				stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), outputArray[k]).convertToByteProcessor());
			}
			Overlay areaOverlay = new Overlay();
			if(numOfAreas>0){
				for(int c=0;c<numOfAreas;c++) {
					for(int r=0;r<areasInEachClass[c].size();r++) {
						drawArea(areasInEachClass[c].get(r),c,areaOverlay);
					}
				}
			}
			ImagePlus marker = new ImagePlus("Marker visualization", stack);
			if(numOfObjectAssociatedMarkers>1){
				marker = HyperStackConverter.toHyperStack(marker, numOfObjectAssociatedMarkers, 1, 1);
			}
			Overlay duplicatedAreaOverlay = new Overlay();
			if(numOfAreas>0){
				for(int c=0;c<numOfAreas;c++) {
					for(int r=0;r<areasInEachClass[c].size();r++) {
						drawAreaForSnapshot(areasInEachClass[c].get(r),c,duplicatedAreaOverlay,markers_mask);
					}
				}
			}
			marker.setOverlay(duplicatedAreaOverlay);
			IJ.save(marker, outputImagePath);
		}
	}
	private void markerMeasurementsAndObjectSnapshots(String outputTextPath, String outputImagePath, int nbCombinations, String[] combinationNames, short[][] markerCombinations)
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			initializeMarkerButtons();
			removeMarkersFromOverlay();
			currentObjectAssociatedMarker = -1;

			ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());

			int[] cellCompartments = new int[3];
			for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
				if(markerCellcompartment[k]==0){
					cellCompartments[0] = 1;
				}
				else if(markerCellcompartment[k]==1){
					cellCompartments[1] = 1;
				}
				else if(markerCellcompartment[k]==2){
					cellCompartments[2] = 1;
				}
			}

			if(!nuclearComponentFlag){
				computeNuclearComponent();
				nuclearComponentFlag = true;
			}
			if((cellCompartments[1]==1)||(cellCompartments[2]==1)){
				if(!innerNuclearComponentFlag){
					computeInnerNuclearComponent();
					innerNuclearComponentFlag = true;
				}
				if(cellCompartments[1]==1){
					if(!membranarComponentFlag){
						computeMembranarComponent();
						membranarComponentFlag = true;
					}
				}
				if(!cytoplasmicComponentFlag){
					computeCytoplasmicComponent();
					cytoplasmicComponentFlag = true;
				}
			}
			List<FloatPolygon> [] nuclearComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], membranarComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], cytoplasmicComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];

			for(int i=0;i<numOfClasses;i++) {
				if(cellCompartments[0]==1){nuclearComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
				if(cellCompartments[1]==1){membranarComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
				if(cellCompartments[2]==1){cytoplasmicComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					if(cellCompartments[0]==1){
						FloatPolygon fp1 = new FloatPolygon();
						nuclearComponentInEachClass[i].add(fp1);
					}
					if(cellCompartments[1]==1){
						FloatPolygon fp2 = new FloatPolygon();
						membranarComponentInEachClass[i].add(fp2);
					}
					if(cellCompartments[2]==1){
						FloatPolygon fp3 = new FloatPolygon();
						cytoplasmicComponentInEachClass[i].add(fp3);
					}
				}
			}
			for(int i=0;i<numOfClasses;i++) {
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						if(cellCompartments[0]==1){
							if(nuclearComponent[i][x][y]>0) {
								nuclearComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
							}
						}
						if(cellCompartments[1]==1){
							if(membranarComponent[i][x][y]>0) {
								membranarComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
						if(cellCompartments[2]==1){
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
			}
			int[][] outputArray = new int[numOfObjectAssociatedMarkers][displayImage.getWidth()*displayImage.getHeight()];

			RoiManager rm_nuclear = new RoiManager();
			ResultsTable rt_nuclear = new ResultsTable(), rt_membranar = new ResultsTable(), rt_cytoplasmic = new ResultsTable(), rt_cell = new ResultsTable();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}

			rt_nuclear = rm_nuclear.multiMeasure(displayImage);
			rm_nuclear.close();

			if(membranarComponentFlag){
				RoiManager rm_membranar = new RoiManager();
				List<Polygon> [] nuclearMembranesInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					nuclearMembranesInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						nuclearMembranesInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								nuclearMembranesInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = nuclearMembranesInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_membranar.addRoi(sr);
					}
				}
				rt_membranar = rm_membranar.multiMeasure(displayImage);
				rm_membranar.close();
			}

			if(cytoplasmicComponentFlag){
				RoiManager rm_cytoplasmic = new RoiManager();
				List<Polygon> [] cytoplasmicInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cytoplasmicInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cytoplasmicInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cytoplasmicInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cytoplasmic.addRoi(sr);
					}
				}
				rt_cytoplasmic = rm_cytoplasmic.multiMeasure(displayImage);
				rm_cytoplasmic.close();
			}

			if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
				int[][][] cellComponent = computeCellComponent();
				RoiManager rm_cell = new RoiManager();
				List<Polygon> [] cellsInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellsInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellsInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cellComponent[i][x][y]>0) {
								cellsInEachClass[i].get(cellComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}

				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cellsInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cell.addRoi(sr);
					}
				}
				rt_cell = rm_cell.multiMeasure(displayImage);
				rm_cell.close();
			}

			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}

			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt_nuclear.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt_nuclear.getValueAsDouble(k, 0), value2 = rt_nuclear.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			int rtIndex=0;
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					finalRt.incrementCounter();
					for(int k=0;k<nbFeatures;k++) {
						if(intensityFeatures[k]==0) {
							finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1), rt_nuclear.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear component", rt_nuclear.getValueAsDouble(rtIndex, c));
							}
							if(membranarComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_membranar.getColumnHeading(k).substring(0, rt_membranar.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear membrane component", rt_membranar.getValueAsDouble(rtIndex, c));
								}}
							if(cytoplasmicComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cytoplasmic.getColumnHeading(k).substring(0, rt_cytoplasmic.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cytoplasmic component", rt_cytoplasmic.getValueAsDouble(rtIndex, c));
								}}
							if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cell.getColumnHeading(k).substring(0, rt_cell.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cell component", rt_cell.getValueAsDouble(rtIndex, c));
								}}
							rtIndex++;
						}
					}
					// object class
					if(numOfClasses>1){
						finalRt.addValue("Object class", i+1);
					}
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];
					// area class
					if((areasInEachClass[0].size()>0)||(numOfAreas>1)){
						boolean areaBool=false;
						if(areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]>(-1)){
							finalRt.addValue("Region class", areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]+1);
							areaBool = true;
						}
						if(!areaBool){
							finalRt.addValue("Region class", 0);
						}
					}
					// combination of markers
					short[] currentMarkerCombination = new short[numOfObjectAssociatedMarkers];
					for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
						int pattern = 0;
						for(int p=0;p<4;p++) {
							for(int q = 0; q < positiveNucleiForEachMarker[k][p].size(); q++) {
								if(positiveNucleiForEachMarker[k][p].get(q)==overlayId){
									pattern = p+1;
								}
							}
						}
						finalRt.addValue("Object marker "+(k+1), pattern);
						if(pattern>0){
							if(nbCombinations==0){
								if(markerCellcompartment[k]==0) {
									FloatPolygon fp = nuclearComponentInEachClass[i].get(j);
									for(int l=0;l<fp.npoints;l++) {
										outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
									}
								}
								else if(markerCellcompartment[k]==1) {
									FloatPolygon fp = membranarComponentInEachClass[i].get(j);
									for(int l=0;l<fp.npoints;l++) {
										outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
									}
								}
								else if(markerCellcompartment[k]==2) {
									FloatPolygon fp = cytoplasmicComponentInEachClass[i].get(j);
									for(int l=0;l<fp.npoints;l++) {
										outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
									}
								}							
							}
							else{
								currentMarkerCombination[k] = 1;
							}
						}
					}
					for(int p=0;p<nbCombinations;p++){
						boolean currentCombination = true;
						for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
							if(currentMarkerCombination[k]!=markerCombinations[p][k]){currentCombination=false;}
						}
						if(currentCombination){
							finalRt.addValue(combinationNames[p], 1);
							for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
								if(currentMarkerCombination[k]==1){
									if(markerCellcompartment[k]==0) {
										FloatPolygon fp = nuclearComponentInEachClass[i].get(j);
										for(int l=0;l<fp.npoints;l++) {
											outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
										}
									}
									else if(markerCellcompartment[k]==1) {
										FloatPolygon fp = membranarComponentInEachClass[i].get(j);
										for(int l=0;l<fp.npoints;l++) {
											outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
										}
									}
									else if(markerCellcompartment[k]==2) {
										FloatPolygon fp = cytoplasmicComponentInEachClass[i].get(j);
										for(int l=0;l<fp.npoints;l++) {
											outputArray[k][(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
										}
									}
								}
							}
						}
						else{
							finalRt.addValue(combinationNames[p], 0);
						}
					}
				}
			}
			finalRt.save(outputTextPath);
			for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
				stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), outputArray[k]).convertToByteProcessor());
			}
			ImagePlus marker = new ImagePlus("Marker visualization", stack);
			if(numOfObjectAssociatedMarkers>1){
				marker = HyperStackConverter.toHyperStack(marker, numOfObjectAssociatedMarkers, 1, 1);
			}
			IJ.save(marker, outputImagePath);
		}
	}
	private void markerMeasurementsAndAreaSnapshots(String outputTextPath, String outputImagePath)
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			initializeMarkerButtons();
			removeMarkersFromOverlay();

			ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());

			int[] outputArray = new int[displayImage.getWidth()*displayImage.getHeight()];

			RoiManager rm_nuclear = new RoiManager();
			ResultsTable rt_nuclear = new ResultsTable(), rt_membranar = new ResultsTable(), rt_cytoplasmic = new ResultsTable(), rt_cell = new ResultsTable();
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					Point[] currentNucleus = objectsInEachClass[i].get(j);
					int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
					for(int p=0;p<xPts.length;p++) {
						xPts[p] = currentNucleus[p].x;
						yPts[p] = currentNucleus[p].y;
					}
					PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
					ShapeRoi sr = new ShapeRoi(pr);
					rm_nuclear.addRoi(sr);
				}
			}
			rt_nuclear = rm_nuclear.multiMeasure(displayImage);
			rm_nuclear.close();

			if(membranarComponentFlag){
				RoiManager rm_membranar = new RoiManager();
				List<Polygon> [] nuclearMembranesInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					nuclearMembranesInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						nuclearMembranesInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(membranarComponent[i][x][y]>0) {
								nuclearMembranesInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = nuclearMembranesInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_membranar.addRoi(sr);
					}
				}
				rt_membranar = rm_membranar.multiMeasure(displayImage);
				rm_membranar.close();
			}

			if(cytoplasmicComponentFlag){
				RoiManager rm_cytoplasmic = new RoiManager();
				List<Polygon> [] cytoplasmicInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cytoplasmicInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cytoplasmicInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cytoplasmicComponent[i][x][y]>0) {
								cytoplasmicInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cytoplasmicInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cytoplasmic.addRoi(sr);
					}
				}
				rt_cytoplasmic = rm_cytoplasmic.multiMeasure(displayImage);
				rm_cytoplasmic.close();
			}

			if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
				int[][][] cellComponent = computeCellComponent();
				RoiManager rm_cell = new RoiManager();
				List<Polygon> [] cellsInEachClass = new ArrayList[MAX_NUM_CLASSES];
				for(int i=0;i<numOfClasses;i++) {
					cellsInEachClass[i] = new ArrayList<Polygon>();
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = new Polygon();
						cellsInEachClass[i].add(fp);
					}
				}
				for(int i=0;i<numOfClasses;i++) {
					for(int y=0;y<displayImage.getHeight();y++) {
						for(int x=0;x<displayImage.getWidth();x++) {
							if(cellComponent[i][x][y]>0) {
								cellsInEachClass[i].get(cellComponent[i][x][y]-1).addPoint(x, y);
							}
						}
					}
				}

				for(int i=0;i<numOfClasses;i++) {
					for(int j=0;j<objectsInEachClass[i].size();j++) {
						Polygon fp = cellsInEachClass[i].get(j);
						int[] xPts = new int[fp.npoints], yPts = new int[fp.npoints];
						for(int p=0;p<fp.npoints;p++) {
							xPts[p] = fp.xpoints[p];
							yPts[p] = fp.ypoints[p];
						}
						PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
						ShapeRoi sr = new ShapeRoi(pr);
						rm_cell.addRoi(sr);
					}
				}
				rt_cell = rm_cell.multiMeasure(displayImage);
				rm_cell.close();
			}

			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}

			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt_nuclear.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt_nuclear.getValueAsDouble(k, 0), value2 = rt_nuclear.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			int rtIndex=0;
			for(int i=0;i<numOfClasses;i++) {
				for(int j=0;j<objectsInEachClass[i].size();j++) {
					finalRt.incrementCounter();
					for(int k=0;k<nbFeatures;k++) {
						if(intensityFeatures[k]==0) {
							finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1), rt_nuclear.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt_nuclear.getColumnHeading(k).substring(0, rt_nuclear.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear component", rt_nuclear.getValueAsDouble(rtIndex, c));
							}
							if(membranarComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_membranar.getColumnHeading(k).substring(0, rt_membranar.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" nuclear membrane component", rt_membranar.getValueAsDouble(rtIndex, c));
								}}
							if(cytoplasmicComponentFlag){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cytoplasmic.getColumnHeading(k).substring(0, rt_cytoplasmic.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cytoplasmic component", rt_cytoplasmic.getValueAsDouble(rtIndex, c));
								}}
							if((membranarComponentFlag)||(cytoplasmicComponentFlag)){
								for(int c=0;c<numOfChannels;c++) {
									finalRt.addValue(rt_cell.getColumnHeading(k).substring(0, rt_cell.getColumnHeading(k).length() - 1)+"Ch"+(c+1)+" cell component", rt_cell.getValueAsDouble(rtIndex, c));
								}}
							rtIndex++;
						}
					}
					if(numOfClasses>1){
						finalRt.addValue("Object class", i+1);
					}
					Point[] pl = objectsInEachClass[i].get(j);
					if((areasInEachClass[0].size()>0)||(numOfAreas>1)){
						boolean areaBool=false;
						if(areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]>(-1)){
							finalRt.addValue("Region class", areaFlag[pl[pl.length/2].x][pl[pl.length/2].y][0]+1);
							areaBool = true;
						}
						if(!areaBool){
							finalRt.addValue("Region class", 0);
						}
					}
				}
			}
			finalRt.save(outputTextPath);

			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), outputArray).convertToByteProcessor());

			Overlay areaOverlay = new Overlay();
			if(numOfAreas>0){
				for(int c=0;c<numOfAreas;c++) {
					for(int r=0;r<areasInEachClass[c].size();r++) {
						drawArea(areasInEachClass[c].get(r),c,areaOverlay);
					}
				}
			}
			ImagePlus marker = new ImagePlus("Marker visualization", stack);
			marker.setOverlay(areaOverlay);
			IJ.save(marker, outputImagePath);
		}
	}
	/** illustration of markers wrt to identified objects */
	void takeMarkerSnapshot() {
		initializeMarkerButtons();
		removeMarkersFromOverlay();
		currentObjectAssociatedMarker = -1;

		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int[][] markers_mask = new int[displayImage.getWidth()][displayImage.getHeight()];

		int[] cellCompartments = new int[3];
		for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
			if(markerCellcompartment[k]==0){
				cellCompartments[0] = 1;
			}
			else if(markerCellcompartment[k]==1){
				cellCompartments[1] = 1;
			}
			else if(markerCellcompartment[k]==2){
				cellCompartments[2] = 1;
			}
		}

		if(!nuclearComponentFlag){
			computeNuclearComponent();
			nuclearComponentFlag = true;
		}
		if((cellCompartments[1]==1)||(cellCompartments[2]==1)){
			if(!innerNuclearComponentFlag){
				computeInnerNuclearComponent();
				innerNuclearComponentFlag = true;
			}
			if(cellCompartments[1]==1){
				if(!membranarComponentFlag){
					computeMembranarComponent();
					membranarComponentFlag = true;
				}
			}
			if(!cytoplasmicComponentFlag){
				computeCytoplasmicComponent();
				cytoplasmicComponentFlag = true;
			}
		}
		List<FloatPolygon> [] nuclearComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], membranarComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], cytoplasmicComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];

		for(int i=0;i<numOfClasses;i++) {
			if(cellCompartments[0]==1){nuclearComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
			if(cellCompartments[1]==1){membranarComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
			if(cellCompartments[2]==1){cytoplasmicComponentInEachClass[i] = new ArrayList<FloatPolygon>();}
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				if(cellCompartments[0]==1){
					FloatPolygon fp1 = new FloatPolygon();
					nuclearComponentInEachClass[i].add(fp1);
				}
				if(cellCompartments[1]==1){
					FloatPolygon fp2 = new FloatPolygon();
					membranarComponentInEachClass[i].add(fp2);
				}
				if(cellCompartments[2]==1){
					FloatPolygon fp3 = new FloatPolygon();
					cytoplasmicComponentInEachClass[i].add(fp3);
				}
			}
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					if(cellCompartments[0]==1){
						if(nuclearComponent[i][x][y]>0) {
							nuclearComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
						}
					}
					if(cellCompartments[1]==1){
						if(membranarComponent[i][x][y]>0) {
							membranarComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
						}
					}
					if(cellCompartments[2]==1){
						if(cytoplasmicComponent[i][x][y]>0) {
							cytoplasmicComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
						}
					}
				}
			}
		}

		for(int k=0;k<numOfObjectAssociatedMarkers;k++) {
			int[] outputArray = new int[displayImage.getWidth()*displayImage.getHeight()];
			for(int p=0;p<4;p++) {
				for(int q = 0; q < positiveNucleiForEachMarker[k][p].size(); q++) {
					int overlayId = positiveNucleiForEachMarker[k][p].get(q), currentClass=0, currentObject=0;;
					for(int i=0;i<numOfClasses;i++) {
						for(int j=0;j<objectsInEachClass[i].size();j++) {
							//Polygon pl = objectsInEachClass[i].get(j).getPolygon();
							Point[] pl = objectsInEachClass[i].get(j);
							if(roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2]==overlayId) {
								currentClass = i;
								currentObject = j;
							}
						}
					}
					if(markerCellcompartment[k]==0) {
						FloatPolygon fp = nuclearComponentInEachClass[currentClass].get(currentObject);
						for(int l=0;l<fp.npoints;l++) {
							outputArray[(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
							markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
						}
					}
					else if(markerCellcompartment[k]==1) {
						FloatPolygon fp = membranarComponentInEachClass[currentClass].get(currentObject);
						for(int l=0;l<fp.npoints;l++) {
							outputArray[(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
							markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
						}
					}
					else if(markerCellcompartment[k]==2) {
						FloatPolygon fp = cytoplasmicComponentInEachClass[currentClass].get(currentObject);
						for(int l=0;l<fp.npoints;l++) {
							outputArray[(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
							markers_mask[(int)fp.xpoints[l]][(int)fp.ypoints[l]] = 1;
						}
					}
				}
			}
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), outputArray).convertToByteProcessor());
		}

		ImagePlus marker = new ImagePlus("Marker visualization", stack);
		if(numOfObjectAssociatedMarkers>1){
			marker = HyperStackConverter.toHyperStack(marker, numOfObjectAssociatedMarkers, 1, 1);
		}
		Overlay duplicatedAreaOverlay = new Overlay();
		if(numOfAreas>0){
			for(int c=0;c<numOfAreas;c++) {
				for(int r=0;r<areasInEachClass[c].size();r++) {
					drawAreaForSnapshot(areasInEachClass[c].get(r),c,duplicatedAreaOverlay,markers_mask);
				}
			}
		}
		marker.setOverlay(duplicatedAreaOverlay);
		marker.show();
	}
	/**
	 * load segmentations
	 */
	private void loadNucleiSegmentations() 
	{

		ImagePlus segmentedImage = IJ.openImage();
		if (null == segmentedImage) return; // user canceled open dialog
		else {

			ImageStack stack = segmentedImage.getStack();
			int[] nucleiDims = segmentedImage.getDimensions();

			// test on nuclei segmentation image dimensions
			if ((nucleiDims[2]>1)&&(nucleiDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[2]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[3]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[0]!=displayImage.getWidth())||(nucleiDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei must be the same dimension than the original image with a number of channels corresponding to the number of classes");
				return; 
			}

			// redimension nuclei segmentation image if needed to fit the expected format
			if (nucleiDims[2]>1){
				segmentedImage = HyperStackConverter.toHyperStack(segmentedImage, 1, nucleiDims[2], 1);
				stack = segmentedImage.getStack();
			}
			else if(nucleiDims[4]>1){
				segmentedImage = HyperStackConverter.toHyperStack(segmentedImage, 1, nucleiDims[4], 1);
				stack = segmentedImage.getStack();
			}
			
			// reinitialize everything
			// roiFlag
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					roiFlag[x][y][0] = -1;
					roiFlag[x][y][1] = -1;
					roiFlag[x][y][2] = -1;
				}
			}
			// overlays
			overlay = new Overlay();
			markersOverlay = new Overlay();
			// objects in each class
			boolean refresh = false;
			if(numOfClasses!=stack.getSize()) {
				refresh = true;
				for(int i=stack.getSize();i<5;i++) {
					classColors[i] = -1;
				}
			}
			for(int c=0;c<numOfClasses;c++) {
				objectsInEachClass[c] = null;
			}
			class2ColorButton.removeActionListener(listener);
			class2RemoveButton.removeActionListener(listener);
			class3ColorButton.removeActionListener(listener);
			class3RemoveButton.removeActionListener(listener);
			class4ColorButton.removeActionListener(listener);
			class4RemoveButton.removeActionListener(listener);
			class5ColorButton.removeActionListener(listener);
			class5RemoveButton.removeActionListener(listener);
			objectsInEachClass = new ArrayList[MAX_NUM_CLASSES];
			objectsInEachClass[0] = new ArrayList<Point[]>();
			numOfClasses = 1;
			for(int c=1;c<stack.getSize();c++) {
				addNewClass();
			}
			if(refresh) {
				//Build GUI
				//win = new CustomWindow(displayImage);
				//win.pack();
				repaintWindow();
			}
			// nuclei markers
			for(int i = 0; i < numOfObjectAssociatedMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
				positivelyLabelledNucleiForEachMarker[i] = null;
				negativelyLabelledNucleiForEachMarker[i] = null;
				featuresForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			positivelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			negativelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			featuresForEachMarker = new ArrayList[MAX_NUM_MARKERS];
					
			numOfObjectAssociatedMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					objectAssociatedMarkersColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				methodToIdentifyObjectAssociatedMarkers[i] = 0;
				channelsForObjectAssociatedMarkers[i] = -1;
				thresholdsForObjectAssociatedMarkers[i][0] = -1;
				thresholdsForObjectAssociatedMarkers[i][1] = -1;
			}
			removeMarker1ButtonFromListener();
			removeMarker2ButtonFromListener();
			removeMarker3ButtonFromListener();
			removeMarker4ButtonFromListener();
			removeMarker5ButtonFromListener();
			removeMarker6ButtonFromListener();
			removeMarker7ButtonFromListener();

			for(int i = 0; i < numOfObjectAssociatedMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = new ArrayList<Short>();
				}
				positivelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				negativelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				featuresForEachMarker[i] = new ArrayList<double[]>();
			}
			for(byte c=0;c<stack.getSize();c++) {
				currentClass = c;
				ImageProcessor ip = stack.getProcessor(c+1);
				int nbRois = 0;
				for(int y=0; y<nucleiDims[1]; y++)
				{
					for(int x=0; x<nucleiDims[0]; x++)
					{
						float value = ip.getf(x,y);
						if((int)value>nbRois){nbRois=(int)value;}
					}
				}

				boolean out=false;

				int minIndex=1, maxIndex=1000, globalCurrentIndex=1;
				if(maxIndex>nbRois) {maxIndex = (int)nbRois;}
				while(!out) {
					List<Integer> [] xCoords = new ArrayList[maxIndex-minIndex+1], yCoords = new ArrayList[maxIndex-minIndex+1];
					int currentIndex=0;
					for(int i = minIndex; i <= maxIndex; i++)
					{
						xCoords[currentIndex] = new ArrayList<Integer>();
						yCoords[currentIndex] = new ArrayList<Integer>();
						currentIndex++;
					}
					for(int y=0; y<nucleiDims[1]; y++)
					{
						for(int x=0; x<nucleiDims[0]; x++)
						{
							float value = ip.getf(x,y);
							if((value>=minIndex)&&(value<=maxIndex)){
								xCoords[(int)value-minIndex].add(x);
								yCoords[(int)value-minIndex].add(y);
							}
						}
					}
					for(int i = minIndex; i <= maxIndex; i++)
					{
						IJ.showProgress(globalCurrentIndex, (int)nbRois);
						if(xCoords[i-minIndex].size()>25) {
							int[] xPoints = new int[xCoords[i-minIndex].size()];
							int[] yPoints = new int[xCoords[i-minIndex].size()];
							for(int u = 0; u< xCoords[i-minIndex].size(); u++)
							{
								xPoints[u] = xCoords[i-minIndex].get(u);
								yPoints[u] = yCoords[i-minIndex].get(u);
							}
							// displaying
							drawNewObjectContour(xPoints,yPoints,currentClass);
							// add nucleus to the list of nuclei
							Point[] roiPoints = new Point[xPoints.length];
							for(int u = 0; u< xPoints.length; u++) {
								roiFlag[(int)xPoints[u]][(int)yPoints[u]][0] = currentClass;
								roiFlag[(int)xPoints[u]][(int)yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
								roiFlag[(int)xPoints[u]][(int)yPoints[u]][2] = (short)(overlay.size()-1);
								roiPoints[u] = new Point(xPoints[u],yPoints[u]);
							}
							// save new nucleus as roi in the corresponding class
							objectsInEachClass[currentClass].add(roiPoints);
						}
						globalCurrentIndex++;
					}
					minIndex = maxIndex+1;
					if(maxIndex==(int)nbRois) {out = true;}
					else
					{
						maxIndex += 1000;
						if(maxIndex>(int)nbRois) {maxIndex = (int)nbRois;}
					}
				}
			}
		}
		currentClass = 0;
		addObjectsToOverlay();
		if(areaDisplayFlag){addAreasToOverlay();visualizeAreasButton1.setSelected(true);}
		else{addAreasFromScratchToOverlayNonVisible();visualizeAreasButton1.setSelected(false);}
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();		
		segmentedImage = null;
	}
	private void loadNucleiSegmentations(ImagePlus segmentedImage) 
	{
		if (null == segmentedImage) return; // user canceled open dialog
		else {
			ImageStack stack = segmentedImage.getStack();
			int[] nucleiDims = segmentedImage.getDimensions();

			// test on nuclei segmentation image dimensions
			if ((nucleiDims[2]>1)&&(nucleiDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[2]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[3]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[0]!=displayImage.getWidth())||(nucleiDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with segmented nuclei must be the same dimension than the original image with a number of channels corresponding to the number of classes");
				return; 
			}

			// redimension nuclei segmentation image if needed to fit the expected format
			if (nucleiDims[2]>1){
				segmentedImage = HyperStackConverter.toHyperStack(segmentedImage, 1, nucleiDims[2], 1);
				stack = segmentedImage.getStack();
			}
			else if(nucleiDims[4]>1){
				segmentedImage = HyperStackConverter.toHyperStack(segmentedImage, 1, nucleiDims[4], 1);
				stack = segmentedImage.getStack();
			}
			// reinitialize everything
			// roiFlag
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					roiFlag[x][y][0] = -1;
					roiFlag[x][y][1] = -1;
					roiFlag[x][y][2] = -1;
				}
			}
			// overlays
			overlay = new Overlay();
			markersOverlay = new Overlay();
			// objects in each class
			boolean refresh = false;
			if(numOfClasses!=stack.getSize()) {
				refresh = true;
				for(int i=stack.getSize();i<5;i++) {
					classColors[i] = -1;
				}
			}
			for(int c=0;c<numOfClasses;c++) {
				objectsInEachClass[c] = null;
			}
			class2ColorButton.removeActionListener(listener);
			class2RemoveButton.removeActionListener(listener);
			class3ColorButton.removeActionListener(listener);
			class3RemoveButton.removeActionListener(listener);
			class4ColorButton.removeActionListener(listener);
			class4RemoveButton.removeActionListener(listener);
			class5ColorButton.removeActionListener(listener);
			class5RemoveButton.removeActionListener(listener);
			objectsInEachClass = new ArrayList[MAX_NUM_CLASSES];
			objectsInEachClass[0] = new ArrayList<Point[]>();
			numOfClasses = 1;
			for(int c=1;c<stack.getSize();c++) {
				addNewClass();
			}
			if(refresh) {
				//Build GUI
				//win = new CustomWindow(displayImage);
				//win.pack();
				repaintWindow();
			}
			// nuclei markers
			for(int i = 0; i < numOfObjectAssociatedMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
				positivelyLabelledNucleiForEachMarker[i] = null;
				negativelyLabelledNucleiForEachMarker[i] = null;
				featuresForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			positivelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			negativelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			featuresForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			
			numOfObjectAssociatedMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					objectAssociatedMarkersColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				methodToIdentifyObjectAssociatedMarkers[i] = 0;
				channelsForObjectAssociatedMarkers[i] = -1;
				thresholdsForObjectAssociatedMarkers[i][0] = -1;
				thresholdsForObjectAssociatedMarkers[i][1] = -1;
			}
			removeMarker1ButtonFromListener();
			removeMarker2ButtonFromListener();
			removeMarker3ButtonFromListener();
			removeMarker4ButtonFromListener();
			removeMarker5ButtonFromListener();
			removeMarker6ButtonFromListener();
			removeMarker7ButtonFromListener();

			for(int i = 0; i < numOfObjectAssociatedMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = new ArrayList<Short>();
				}
				positivelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				negativelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				featuresForEachMarker[i] = new ArrayList<double[]>();
			}
			for(byte c=0;c<stack.getSize();c++) {
				currentClass = c;
				ImageProcessor ip = stack.getProcessor(c+1);
				int nbRois = 0;
				for(int y=0; y<nucleiDims[1]; y++)
				{
					for(int x=0; x<nucleiDims[0]; x++)
					{
						float value = ip.getf(x,y);
						if((int)value>nbRois){nbRois=(int)value;}
					}
				}
				boolean out=false;

				int minIndex=1, maxIndex=1000, globalCurrentIndex=1;
				if(maxIndex>nbRois) {maxIndex = (int)nbRois;}
				while(!out) {
					List<Integer> [] xCoords = new ArrayList[maxIndex-minIndex+1], yCoords = new ArrayList[maxIndex-minIndex+1];
					int currentIndex=0;
					for(int i = minIndex; i <= maxIndex; i++)
					{
						xCoords[currentIndex] = new ArrayList<Integer>();
						yCoords[currentIndex] = new ArrayList<Integer>();
						currentIndex++;
					}
					for(int y=0; y<nucleiDims[1]; y++)
					{
						for(int x=0; x<nucleiDims[0]; x++)
						{
							float value = ip.getf(x,y);
							if((value>=minIndex)&&(value<=maxIndex)){
								xCoords[(int)value-minIndex].add(x);
								yCoords[(int)value-minIndex].add(y);
							}
						}
					}
					for(int i = minIndex; i <= maxIndex; i++)
					{
						IJ.showProgress(globalCurrentIndex, (int)nbRois);
						if(xCoords[i-minIndex].size()>25) {
							int[] xPoints = new int[xCoords[i-minIndex].size()];
							int[] yPoints = new int[xCoords[i-minIndex].size()];
							for(int u = 0; u< xCoords[i-minIndex].size(); u++)
							{
								xPoints[u] = xCoords[i-minIndex].get(u);
								yPoints[u] = yCoords[i-minIndex].get(u);
							}
							// displaying
							drawNewObjectContour(xPoints,yPoints,currentClass);
							// add nucleus to the list of nuclei
							Point[] roiPoints = new Point[xPoints.length];
							for(int u = 0; u< xPoints.length; u++) {
								roiFlag[(int)xPoints[u]][(int)yPoints[u]][0] = currentClass;
								roiFlag[(int)xPoints[u]][(int)yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
								roiFlag[(int)xPoints[u]][(int)yPoints[u]][2] = (short)(overlay.size()-1);
								roiPoints[u] = new Point(xPoints[u],yPoints[u]);
							}
							// save new nucleus as roi in the corresponding class
							objectsInEachClass[currentClass].add(roiPoints);
						}
						globalCurrentIndex++;
					}
					minIndex = maxIndex+1;
					if(maxIndex==(int)nbRois) {out = true;}
					else
					{
						maxIndex += 1000;
						if(maxIndex>(int)nbRois) {maxIndex = (int)nbRois;}
					}
				}
			}
		}
		currentClass = 0;
		addObjectsToOverlay();
		if(areaDisplayFlag){addAreasToOverlay();visualizeAreasButton1.setSelected(true);}
		else{addAreasFromScratchToOverlayNonVisible();visualizeAreasButton1.setSelected(false);}
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();		
		segmentedImage = null;
		//Build GUI
		repaintWindow();
	}

	/**
	 * load marker identification
	 */
	private void loadObjectAssociatedMarkerIdentifications() 
	{
		ImagePlus markerImage = IJ.openImage();
		if (null == markerImage) return; // user canceled open dialog
		else {

			ImageStack stack = markerImage.getStack();
			int[] markerDims = markerImage.getDimensions();

			// test on nuclei segmentation image dimensions
			if ((markerDims[2]>1)&&(markerDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the object(s)");
				return;
			}
			if ((markerDims[2]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the object(s)");
				return;
			}
			if ((markerDims[3]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the object(s)");
				return;
			}
			if ((markerDims[0]!=displayImage.getWidth())||(markerDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects must be the same dimension than the original image with a number of channels corresponding to the number of object(s)");
				return; 
			}

			// redimension nuclei segmentation image if needed to fit the expected format
			if (markerDims[2]>1){
				markerImage = HyperStackConverter.toHyperStack(markerImage, 1, markerDims[2], 1);
				stack = markerImage.getStack();
			}
			else if(markerDims[4]>1){
				markerImage = HyperStackConverter.toHyperStack(markerImage, 1, markerDims[4], 1);
				stack = markerImage.getStack();
			}

			// reinitialization
			// markers overlay
			for(int y=0; y<markerDims[1]; y++)
			{
				for(int x=0; x<markerDims[0]; x++)
				{
					if(roiFlag[x][y][2]>(-1)) {
						markersOverlay.get(roiFlag[x][y][2]).setStrokeColor(colors[classColors[roiFlag[x][y][0]]]);
						markersOverlay.get(roiFlag[x][y][2]).setStrokeWidth(0);
					}
				}
			}
			// nuclei markers
			for(int i = 0; i < numOfObjectAssociatedMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
				positivelyLabelledNucleiForEachMarker[i] = null;
				negativelyLabelledNucleiForEachMarker[i] = null;
				featuresForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			positivelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			negativelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			featuresForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			
			numOfObjectAssociatedMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					objectAssociatedMarkersColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				methodToIdentifyObjectAssociatedMarkers[i] = 0;
				channelsForObjectAssociatedMarkers[i] = -1;
				thresholdsForObjectAssociatedMarkers[i][0] = -1;
				thresholdsForObjectAssociatedMarkers[i][1] = -1;
			}
			removeMarker1ButtonFromListener();
			removeMarker2ButtonFromListener();
			removeMarker3ButtonFromListener();
			removeMarker4ButtonFromListener();
			removeMarker5ButtonFromListener();
			removeMarker6ButtonFromListener();
			removeMarker7ButtonFromListener();

			for(int i = 0; i < stack.getSize(); i++) {
				boolean keepGoing = addNewMarker();
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = new ArrayList<Short>();
				}
				positivelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				negativelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				featuresForEachMarker[i] = new ArrayList<double[]>();
			}

			// load nuclei markers
			for(int c=0;c<stack.getSize();c++) {
				ImageProcessor ip = stack.getProcessor(c+1);
				int maxValue=0;
				for(int y=0; y<markerDims[1]; y++)
				{
					for(int x=0; x<markerDims[0]; x++)
					{
						int value = (int)ip.getf(x,y);
						if(value>maxValue) {maxValue = value;}
					}
				}
				if(maxValue>4) {
					for(int y=0; y<markerDims[1]; y++)
					{
						for(int x=0; x<markerDims[0]; x++)
						{
							int value = (int)ip.getf(x,y);
							if(value>0){
								ip.setf(x, y, 1);
							}
						}
					}
				}
				for(int y=0; y<markerDims[1]; y++)
				{
					for(int x=0; x<markerDims[0]; x++)
					{

						int value = (int)ip.getf(x,y);
						if(value>0){
							if(roiFlag[x][y][2]>(-1)) {
								boolean add=true;
								for(int p=0;p<4;p++) {
									for(int i = 0; i < positiveNucleiForEachMarker[c][p].size(); i++) {
										if(positiveNucleiForEachMarker[c][p].get(i)==roiFlag[x][y][2]) {
											add = false;
										}
									}
								}
								if(add) {
									positiveNucleiForEachMarker[c][value-1].add(roiFlag[x][y][2]);
								}
							}
						}
					}
				}
			}
		}
		currentObjectAssociatedMarker = -1;

		//Build GUI
		//win = new CustomWindow(displayImage);
		//win.pack();
		repaintWindow();
		
		// refresh overlay
		addObjectsToOverlay();
		addAreasToOverlay();
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
		markerImage = null;
	}
	/**
	 * load marker identification
	 */
	private void loadObjectAssociatedMarkerIdentifications(ImagePlus markerImage) 
	{
		if (null == markerImage) return; // user canceled open dialog
		else {

			ImageStack stack = markerImage.getStack();
			int[] markerDims = markerImage.getDimensions();

			// test on nuclei segmentation image dimensions
			if ((markerDims[2]>1)&&(markerDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the object(s)");
				return;
			}
			if ((markerDims[2]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the object(s)");
				return;
			}
			if ((markerDims[3]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the object(s)");
				return;
			}
			if ((markerDims[0]!=displayImage.getWidth())||(markerDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with annotated objects must be the same dimension than the original image with a number of channels corresponding to the number of object(s)");
				return; 
			}

			// redimension nuclei segmentation image if needed to fit the expected format
			if (markerDims[2]>1){
				markerImage = HyperStackConverter.toHyperStack(markerImage, 1, markerDims[2], 1);
				stack = markerImage.getStack();
			}
			else if(markerDims[4]>1){
				markerImage = HyperStackConverter.toHyperStack(markerImage, 1, markerDims[4], 1);
				stack = markerImage.getStack();
			}

			// reinitialization
			// markers overlay
			for(int y=0; y<markerDims[1]; y++)
			{
				for(int x=0; x<markerDims[0]; x++)
				{
					if(roiFlag[x][y][2]>(-1)) {
						markersOverlay.get(roiFlag[x][y][2]).setStrokeColor(colors[classColors[roiFlag[x][y][0]]]);
						markersOverlay.get(roiFlag[x][y][2]).setStrokeWidth(0);
					}
				}
			}
			// nuclei markers
			for(int i = 0; i < numOfObjectAssociatedMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
				positivelyLabelledNucleiForEachMarker[i] = null;
				negativelyLabelledNucleiForEachMarker[i] = null;
				featuresForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			positivelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			negativelyLabelledNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			featuresForEachMarker = new ArrayList[MAX_NUM_MARKERS];
			
			numOfObjectAssociatedMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					objectAssociatedMarkersColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				methodToIdentifyObjectAssociatedMarkers[i] = 0;
				methodToIdentifyObjectAssociatedMarkers[i] = 0;
				channelsForObjectAssociatedMarkers[i] = -1;
				thresholdsForObjectAssociatedMarkers[i][0] = -1;
				thresholdsForObjectAssociatedMarkers[i][1] = -1;
			}
			removeMarker1ButtonFromListener();
			removeMarker2ButtonFromListener();
			removeMarker3ButtonFromListener();
			removeMarker4ButtonFromListener();
			removeMarker5ButtonFromListener();
			removeMarker6ButtonFromListener();
			removeMarker7ButtonFromListener();

			for(int i = 0; i < stack.getSize(); i++) {
				boolean keepGoing = addNewMarker();
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = new ArrayList<Short>();
				}
				positivelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				negativelyLabelledNucleiForEachMarker[i] = new ArrayList<Short>();
				featuresForEachMarker[i] = new ArrayList<double[]>();
			}

			// load nuclei markers
			for(int c=0;c<stack.getSize();c++) {
				ImageProcessor ip = stack.getProcessor(c+1);
				int maxValue=0;
				for(int y=0; y<markerDims[1]; y++)
				{
					for(int x=0; x<markerDims[0]; x++)
					{
						int value = (int)ip.getf(x,y);
						if(value>maxValue) {maxValue = value;}
					}
				}
				if(maxValue>4) {
					for(int y=0; y<markerDims[1]; y++)
					{
						for(int x=0; x<markerDims[0]; x++)
						{
							int value = (int)ip.getf(x,y);
							if(value>0){
								ip.setf(x, y, 1);
							}
						}
					}
				}
				for(int y=0; y<markerDims[1]; y++)
				{
					for(int x=0; x<markerDims[0]; x++)
					{

						int value = (int)ip.getf(x,y);
						if(value>0){
							if(roiFlag[x][y][2]>(-1)) {
								boolean add=true;
								for(int p=0;p<4;p++) {
									for(int i = 0; i < positiveNucleiForEachMarker[c][p].size(); i++) {
										if(positiveNucleiForEachMarker[c][p].get(i)==roiFlag[x][y][2]) {
											add = false;
										}
									}
								}
								if(add) {
									positiveNucleiForEachMarker[c][value-1].add(roiFlag[x][y][2]);
								}
							}
						}
					}
				}
			}
		}
		currentObjectAssociatedMarker = -1;

		//Build GUI
		//win = new CustomWindow(displayImage);
		//win.pack();
		repaintWindow(); 
		
		// refresh overlay
		addObjectsToOverlay();
		addAreasToOverlay();
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
		markerImage = null;
	}
	/**
	 * load areas
	 */
	private void loadAreas() 
	{
		ImagePlus areaImage = IJ.openImage();
		if (null == areaImage) return; // user canceled open dialog
		else {

			ImageStack stack = areaImage.getStack();
			int[] nucleiDims = areaImage.getDimensions();

			// test on nuclei segmentation image dimensions
			if ((nucleiDims[2]>1)&&(nucleiDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with areas cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[2]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with areas cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[3]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with areas cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[0]!=displayImage.getWidth())||(nucleiDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with areas must be the same dimension than the original image with a number of channels corresponding to the number of classes");
				return; 
			}

			// redimension nuclei segmentation image if needed to fit the expected format
			if (nucleiDims[2]>1){
				areaImage = HyperStackConverter.toHyperStack(areaImage, 1, nucleiDims[2], 1);
				stack = areaImage.getStack();
			}
			else if(nucleiDims[4]>1){
				areaImage = HyperStackConverter.toHyperStack(areaImage, 1, nucleiDims[4], 1);
				stack = areaImage.getStack();
			}
			// overlays
			removeAreasFromOverlay();
			// reinitialize everything
			// areaFlag
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					areaFlag[x][y][0] = -1;
					areaFlag[x][y][1] = -1;
					areaFlag[x][y][2] = -1;
				}
			}
			// areas in each class
			boolean refresh = false;
			if(numOfAreas!=stack.getSize()) {
				refresh = true;
				for(int i=stack.getSize();i<5;i++) {
					areaColors[i] = -1;
				}
			}
			for(int c=0;c<numOfAreas;c++) {
				areasInEachClass[c] = null;
			}
			area2ColorButton.removeActionListener(listener);
			area2RemoveButton.removeActionListener(listener);
			area3ColorButton.removeActionListener(listener);
			area3RemoveButton.removeActionListener(listener);
			area4ColorButton.removeActionListener(listener);
			area4RemoveButton.removeActionListener(listener);
			area5ColorButton.removeActionListener(listener);
			area5RemoveButton.removeActionListener(listener);
			areasInEachClass = new ArrayList[MAX_NUM_CLASSES];
			areasInEachClass[0] = new ArrayList<Point[]>();
			numOfAreas = 1;
			updateAreaButtons(0);
			for(int c=1;c<stack.getSize();c++) {
				addNewArea();
			}
			if(refresh) {
				//Build GUI
				//win = new CustomWindow(displayImage);
				//win.pack();
				repaintWindow();
			}
			updateAreaButtons(0);

			for(byte c=0;c<stack.getSize();c++) {
				currentArea = c;
				ImageProcessor ip = stack.getProcessor(c+1);
				
				int nbPts=0;
				for(int y=0; y<nucleiDims[1]; y++)
				{
					for(int x=0; x<nucleiDims[0]; x++)
					{
						float value = ip.getf(x,y);
						if((int)value>0){
							nbPts++;
						}
					}
				}
				Point[] pts = new Point[nbPts];
				int index=0;
				for(int y=0; y<nucleiDims[1]; y++)
				{
					for(int x=0; x<nucleiDims[0]; x++)
					{
						float value = ip.getf(x,y);
						if((int)value>0){
							pts[index] = new Point(x, y); 
							areaFlag[x][y][0] = currentArea;
							areaFlag[x][y][1] = (short)areasInEachClass[currentArea].size();
							areaFlag[x][y][2] = (short)overlay.size();
							index++;
						}
					}
				}
				// displaying
				drawArea(pts, currentArea);
				areasInEachClass[currentArea].add(pts);
			}
		}
		currentArea = 0;
		addAreasToOverlay();
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();		
		areaImage = null;
	}
	private void loadDataForLogisticRegression(int markerToBeLoaded) 
	{
		OpenDialog od = new OpenDialog("Open file with data for classifier", "");
        String directory = od.getDirectory();
        String name = od.getFileName();
		if (null == od) return; // user canceled open dialog

        List<List<String>> records = new ArrayList<>();
        try (BufferedReader br = new BufferedReader(new FileReader(directory + name))) {
            String line;
            while ((line = br.readLine()) != null) {
                String[] values = line.split(",");
                records.add(Arrays.asList(values));
            }
        }
		catch(IOException ioe){
			IJ.log("Problem when loading the data.");
			return;
		}
        		
		// update cell compartment marker status
		if(markerCellcompartment[markerToBeLoaded] == 0) {
			if(records.get(0).get(1).equals("Nuclear membrane")){
				IJ.showMessage("Incompatible marker", "You loaded data for a nuclear membrane marker while you created a new nuclear marker, which is not possible");
				return;
			}
			if(records.get(0).get(1).equals("Cytoplasmic")){
				IJ.showMessage("Incompatible marker", "You loaded data for a cytoplasmic marker while you created a new nuclear marker, which is not possible");
				return;
			}
		}
		else if(markerCellcompartment[markerToBeLoaded] == 1) {
			if(records.get(0).get(1).equals("Nuclear")){
				IJ.showMessage("Incompatible marker", "You loaded data for a nuclear marker while you created a new nuclear membrane marker, which is not possible");
				return;
			}
			if(records.get(0).get(1).equals("Cytoplasmic")){
				IJ.showMessage("Incompatible marker", "You loaded data for a cytoplasmic marker while you created a new nuclear membrane marker, which is not possible");
				return;
			}
		}
		else if(markerCellcompartment[markerToBeLoaded] == 2) {
			if(records.get(0).get(1).equals("Nuclear")){
				IJ.showMessage("Incompatible marker", "You loaded data for a nuclear marker while you created a new cytoplasmic marker, which is not possible");
				return;
			}
			if(records.get(0).get(1).equals("Nuclear membrane")){
				IJ.showMessage("Incompatible marker", "You loaded data for a nuclear membrane marker while you created a new cytoplasmic marker, which is not possible");
				return;
			}
		}

		for(int i=2;i<records.size();i++){
			double[] features = new double[nbFeatures];
			for(int p=0;p<nbFeatures;p++){
						features[p] = Double.valueOf(records.get(i).get(p));
			}							
			featuresForEachMarker[markerToBeLoaded].add(features);
		}
		removeMarkersFromOverlay();
		removeObjectAssociatedMarkerForML(markerToBeLoaded);
		train(markerToBeLoaded);
	}
	private void loadAreas(ImagePlus areaImage) 
	{
		if (null == areaImage) return; // user canceled open dialog
		else {
			ImageStack stack = areaImage.getStack();
			int[] nucleiDims = areaImage.getDimensions();

			// test on nuclei segmentation image dimensions
			if ((nucleiDims[2]>1)&&(nucleiDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with areas cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[2]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with areas cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[3]>1)&&(nucleiDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with areas cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((nucleiDims[0]!=displayImage.getWidth())||(nucleiDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with areas must be the same dimension than the original image with a number of channels corresponding to the number of classes");
				return; 
			}

			// redimension nuclei segmentation image if needed to fit the expected format
			if (nucleiDims[2]>1){
				areaImage = HyperStackConverter.toHyperStack(areaImage, 1, nucleiDims[2], 1);
				stack = areaImage.getStack();
			}
			else if(nucleiDims[4]>1){
				areaImage = HyperStackConverter.toHyperStack(areaImage, 1, nucleiDims[4], 1);
				stack = areaImage.getStack();
			}
			// reinitialize everything
			// roiFlag
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					areaFlag[x][y][0] = -1;
					areaFlag[x][y][1] = -1;
					areaFlag[x][y][2] = -1;
				}
			}
			// overlays
			removeAreasFromOverlay();
			// areas in each class
			boolean refresh = false;
			if(numOfAreas!=stack.getSize()) {
				refresh = true;
				for(int i=stack.getSize();i<5;i++) {
					areaColors[i] = -1;
				}
			}
			for(int c=0;c<numOfAreas;c++) {
				areasInEachClass[c] = null;
			}
			area2ColorButton.removeActionListener(listener);
			area2RemoveButton.removeActionListener(listener);
			area3ColorButton.removeActionListener(listener);
			area3RemoveButton.removeActionListener(listener);
			area4ColorButton.removeActionListener(listener);
			area4RemoveButton.removeActionListener(listener);
			area5ColorButton.removeActionListener(listener);
			area5RemoveButton.removeActionListener(listener);
			areasInEachClass = new ArrayList[MAX_NUM_CLASSES];
			areasInEachClass[0] = new ArrayList<Point[]>();
			numOfAreas = 1;
			updateAreaButtons(0);
			for(int c=1;c<stack.getSize();c++) {
				addNewArea();
			}
			if(refresh) {
				//Build GUI
				//win = new CustomWindow(displayImage);
				//win.pack();
				repaintWindow();
			}

			for(byte c=0;c<stack.getSize();c++) {
				currentArea = c;
				ImageProcessor ip = stack.getProcessor(c+1);
				int nbRois = 0;
				for(int y=0; y<nucleiDims[1]; y++)
				{
					for(int x=0; x<nucleiDims[0]; x++)
					{
						float value = ip.getf(x,y);
						if((int)value>nbRois){nbRois=(int)value;}
					}
				}

				for(int i = 0; i < (int)nbRois; i++)
				{
					int nbPts=0;
					for(int y=0; y<nucleiDims[1]; y++)
					{
						for(int x=0; x<nucleiDims[0]; x++)
						{
							float value = ip.getf(x,y);
							if((int)value==(i+1)){
								nbPts++;
							}
						}
					}
					Point[] pts = new Point[nbPts];
					int index=0;
					for(int y=0; y<nucleiDims[1]; y++)
					{
						for(int x=0; x<nucleiDims[0]; x++)
						{
							float value = ip.getf(x,y);
							if((int)value==(i+1)){
								pts[index] = new Point(x, y); 
								areaFlag[x][y][0] = currentArea;
								areaFlag[x][y][1] = (short)areasInEachClass[currentArea].size();
								areaFlag[x][y][2] = (short)overlay.size();
								index++;
							}
						}
					}
					// displaying
					drawArea(pts, currentArea);
					areasInEachClass[currentArea].add(pts);
				}
			}
		}
		currentArea = 0;
		addAreasToOverlay();
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();		
		areaImage = null;
	}
	/**
	 * save nuclei segmentations
	 */
	private void saveNucleiSegmentation() 
	{
		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());

		for(int c=0;c<numOfClasses;c++) {
			int[] nucleiMasks = new int[displayImage.getWidth()*displayImage.getHeight()];
			for(int i=0;i<objectsInEachClass[c].size();i++) {
				//int[] xPts = objectsInEachClass[c].get(i).getPolygon().xpoints;
				//int[] yPts = objectsInEachClass[c].get(i).getPolygon().ypoints;
				Point[] fp = objectsInEachClass[c].get(i);
				for(int j=0;j<fp.length;j++) {
					nucleiMasks[fp[j].y*displayImage.getWidth()+fp[j].x] = i+1;
				}
			}
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), nucleiMasks));
		}
		ImagePlus segmentednuclei = new ImagePlus("Segmented objects", stack);
		SaveDialog sd = new SaveDialog("Object segmentation", "ObjectSegmentation", ".tif");
		final String dir = sd.getDirectory();
		final String filename = sd.getFileName();

		if(null == dir || null == filename)
			return;

		IJ.save(segmentednuclei, dir + filename);
	}
	/**
	 * save nuclear marker identifications
	 */
	private void saveObjectAssociatedMarkerIdentifications() 
	{
		SaveDialog sd = new SaveDialog("Identified objects", "IdentifiedObjects", ".tif");
		final String dir = sd.getDirectory();
		final String filename = sd.getFileName();

		if(null == dir || null == filename)
			return;

		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int maxOverlayId=0;
		for(int c=0;c<numOfObjectAssociatedMarkers;c++) {
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					if(roiFlag[x][y][2]>maxOverlayId) {maxOverlayId = roiFlag[x][y][2];} 
				}
			}
		}
		Point[] roiFlagCorrespondence = new Point[maxOverlayId+1];
		for(int i=0;i<=maxOverlayId;i++) {
			roiFlagCorrespondence[i] = new Point(-1,-1);
		}
		for(int y=0;y<displayImage.getHeight();y++) {
			for(int x=0;x<displayImage.getWidth();x++) {
				if(roiFlag[x][y][2]>(-1)) {
					if(roiFlagCorrespondence[roiFlag[x][y][2]].x==(-1)) {
						Point correspondingRoiFlagAttributes = new Point(roiFlag[x][y][0],roiFlag[x][y][1]);
						roiFlagCorrespondence[roiFlag[x][y][2]] = correspondingRoiFlagAttributes;
					}
				}
			}
		}
		for(int c=0;c<numOfObjectAssociatedMarkers;c++) {
			int[] nucleiMarker = new int[displayImage.getWidth()*displayImage.getHeight()];
			for(int p=0;p<4;p++) {
				for(short k=0;k<positiveNucleiForEachMarker[c][p].size();k++) {
					if(positiveNucleiForEachMarker[c][p].size()>0) {
						Point[] fp = objectsInEachClass[roiFlagCorrespondence[positiveNucleiForEachMarker[c][p].get(k)].x].get(roiFlagCorrespondence[positiveNucleiForEachMarker[c][p].get(k)].y);
						for(int i=0;i<fp.length;i++) {
							nucleiMarker[fp[i].y*displayImage.getWidth()+fp[i].x] = p+1;
						}
					}
				}
			}
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), nucleiMarker).convertToByteProcessor());
		}
		ImagePlus segmentednuclei = new ImagePlus("Marker objects", stack);

		IJ.save(segmentednuclei, dir + filename);
	}
	private void saveObjectAssociatedMarkerIdentifications(String outputFilename) 
	{
		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int maxOverlayId=0;
		for(int c=0;c<numOfObjectAssociatedMarkers;c++) {
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					if(roiFlag[x][y][2]>maxOverlayId) {maxOverlayId = roiFlag[x][y][2];} 
				}
			}
		}
		Point[] roiFlagCorrespondence = new Point[maxOverlayId+1];
		for(int i=0;i<=maxOverlayId;i++) {
			roiFlagCorrespondence[i] = new Point(-1,-1);
		}
		for(int y=0;y<displayImage.getHeight();y++) {
			for(int x=0;x<displayImage.getWidth();x++) {
				if(roiFlag[x][y][2]>(-1)) {
					if(roiFlagCorrespondence[roiFlag[x][y][2]].x==(-1)) {
						Point correspondingRoiFlagAttributes = new Point(roiFlag[x][y][0],roiFlag[x][y][1]);
						roiFlagCorrespondence[roiFlag[x][y][2]] = correspondingRoiFlagAttributes;
					}
				}
			}
		}
		for(int c=0;c<numOfObjectAssociatedMarkers;c++) {
			int[] nucleiMarker = new int[displayImage.getWidth()*displayImage.getHeight()];
			for(int p=0;p<4;p++) {
				for(short k=0;k<positiveNucleiForEachMarker[c][p].size();k++) {
					if(positiveNucleiForEachMarker[c][p].size()>0) {
						//Polygon fp = objectsInEachClass[roiFlagCorrespondence[positiveNucleiForEachMarker[c][p].get(k)].x].get(roiFlagCorrespondence[positiveNucleiForEachMarker[c][p].get(k)].y).getPolygon();
						Point[] fp = objectsInEachClass[roiFlagCorrespondence[positiveNucleiForEachMarker[c][p].get(k)].x].get(roiFlagCorrespondence[positiveNucleiForEachMarker[c][p].get(k)].y);
						//int[] xPoints = fp.xpoints, yPoints = fp.ypoints;
						for(int i=0;i<fp.length;i++) {
							nucleiMarker[fp[i].y*displayImage.getWidth()+fp[i].x] = p+1;
						}
					}
				}
			}
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), nucleiMarker).convertToByteProcessor());
		}
		ImagePlus segmentednuclei = new ImagePlus("Marker objectss", stack);

		IJ.save(segmentednuclei, outputFilename);
	}
	/**
	 * save areas
	 */
	private void saveAreas() 
	{
		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());

		for(int c=0;c<numOfAreas;c++) {
			int[] areaMasks = new int[displayImage.getWidth()*displayImage.getHeight()];
			for(int i=0;i<areasInEachClass[c].size();i++) {
				Point[] fp = areasInEachClass[c].get(i);
				for(int j=0;j<fp.length;j++) {
					areaMasks[fp[j].y*displayImage.getWidth()+fp[j].x] = 255;
				}
			}
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), areaMasks).convertToByteProcessor());
		}
		ImagePlus areaImage = new ImagePlus("Regions", stack);
		SaveDialog sd = new SaveDialog("Regions", "Regions", ".tif");
		final String dir = sd.getDirectory();
		final String filename = sd.getFileName();

		if(null == dir || null == filename)
			return;

		IJ.save(areaImage, dir + filename);
	}
	/**
	 * save data for classifier
	 */
	private void saveDataForLogisticRegression(int markerToBeSaved) 
	{
		SaveDialog sd = new SaveDialog("Data for classifier", "ClassifierData", ".csv");
		final String dir = sd.getDirectory();
		final String filename = sd.getFileName();

		if(null == dir || null == filename)
			return;

		ArrayList<double[]> output = featuresToBeSaved(markerToBeSaved);
		
		String outputFilename = dir + filename;
		
		try{
			FileWriter csvWriter = new FileWriter(outputFilename);
			csvWriter.append("Compartment,");
			if(markerCellcompartment[markerToBeSaved]==0) {
				csvWriter.append("Nuclear\n");
			}
			else{
				if(markerCellcompartment[markerToBeSaved]==1) {
					csvWriter.append("Nuclear membrane\n");
				}
				else{
					if(markerCellcompartment[markerToBeSaved]==2) {
						csvWriter.append("Cytoplasmic\n");
					}
				}
			}
			csvWriter.append("Average intensity,Standard deviation intensity,Nuclear circularity,Size,Class\n");

			for (int i=0; i<output.size(); i++) {
				csvWriter.append(String.valueOf(output.get(i)[0]));
				csvWriter.append(",");
				csvWriter.append(String.valueOf(output.get(i)[1]));
				csvWriter.append(",");
				csvWriter.append(String.valueOf(output.get(i)[2]));
				csvWriter.append(",");
				csvWriter.append(String.valueOf(output.get(i)[3]));
				csvWriter.append(",");
				csvWriter.append(String.valueOf(output.get(i)[4]));
				csvWriter.append("\n");
			}

			csvWriter.flush();
			csvWriter.close();
		}
		catch(IOException ioe){
			IJ.log("Problem when saving the data.");
			return;
		}
	}

	/**
	 * Repaint whole window
	 */
	private void repaintWindow() 
	{
		// Repaint window
		win = new CustomWindow(displayImage);
		win.pack();
		// refresh overlay
		if(currentMode==0) {
			displayImage.setOverlay(overlay);
			displayImage.updateAndDraw();
		}
		else {
			displayImage.setOverlay(markersOverlay);
			displayImage.updateAndDraw();
		}
	}

}