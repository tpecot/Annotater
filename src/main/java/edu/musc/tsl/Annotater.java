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
import java.io.File;

import fiji.util.gui.GenericDialogPlus;
import fiji.util.gui.OverlayedImageCanvas;
import ij.IJ;
import ij.io.DirectoryChooser;
import ij.io.OpenDialog;
import ij.io.Opener;
import ij.plugin.frame.RoiManager;
import ij.ImagePlus;
import ij.ImageStack;
import ij.WindowManager;
import ij.gui.FreehandRoi;
import ij.gui.ImageWindow;
import ij.gui.Overlay;
import ij.gui.PointRoi;
import ij.gui.PolygonRoi;
import ij.gui.Roi;
import ij.gui.RoiProperties;
import ij.gui.ShapeRoi;
import ij.gui.Wand;
import ij.gui.Toolbar;
import ij.io.SaveDialog;
import ij.plugin.CompositeConverter;
import ij.plugin.HyperStackConverter;
import ij.plugin.filter.Analyzer;
import ij.process.ImageConverter;
import ij.process.FloatPolygon;
import ij.process.FloatProcessor;
import ij.process.ImageProcessor;
import ij.process.ImageStatistics;
import ij.process.LUT;
import ij.process.EllipseFitter;
import ij.measure.ResultsTable;
import ij.macro.Interpreter;
import ij.Macro;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Panel;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.Polygon;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JRadioButton;
import javax.swing.JSlider;
import javax.swing.JTextField;
import javax.swing.JTextArea;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.ButtonGroup;

/**
 * This example illustrates how to create an ImageJ {@link Command} plugin.
 * <p>
 * The code here is a simple Gaussian blur using ImageJ Ops.
 * </p>
 * <p>
 * You should replace the parameter fields with your own inputs and outputs,
 * and replace the {@link run} method implementation with your own logic.
 * </p>
 */
@Plugin(type = Command.class, menuPath = "Plugins>Annotater")
public class Annotater<T extends RealType<T>> implements Command {
	
	String imageFilePath;
	/** maximum number of classes (labels) allowed on the GUI*/
	private static final int MAX_NUM_CLASSES = 5;
	private static final int MAX_NUM_MARKERS = 7;
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
	/** overlay to display the objects for each class */
	private Overlay markersOverlay;
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
	
	/** marker currently annotated **/
	private int currentMarker = -1;
	/** pattern for channel currently annotated **/
	private int currentPattern = -1;
	/** array of lists of positively marked Rois for each channel */
	private List<Short> [][] positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
	/** array of lists of Rois for each class */
	
	/** nuclei annotation mode button */
	private JRadioButton nucleiAnnotationButton;
	/** marker annotation mode button */
	private JRadioButton nucleiMarkerButton;

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
	
	/** create a new ROI listener to add ROI for each object **/
	RoiListener roiListener;
	/** create a new KeyAction to allow the user to interact with the keyboard for navigation**/
	KeyActions keyListener;
	
	/** available colors for available classes*/
	private final Color[] colors = new Color[]{Color.red, Color.green, Color.blue, Color.yellow, Color.magenta, Color.cyan, Color.orange, Color.pink, Color.black, Color.gray, Color.white};

	/** color indices for classes */
	private byte[] classColors = new byte[]{0, -1, -1, -1, -1};
	/** color indices for markers */
	private byte[][] markerColors = new byte[][]{{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7},{4, 5, 6, 7}};
	/** cell compartment index for markers: 0 -> nuclear, 1 -> membranar, 2 -> cytoplasmic */
	private byte[] markerCellcompartment = new byte[]{0,0,0,0,0,0,0};
	/** channel to be thresholded */
	private byte[] channelForMarker = new byte[]{-1,-1,-1,-1,-1,-1,-1};
	/** thresholds */
	private int[][] thresholdForMarker = new int[][]{{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1}};
	/** current number of classes */
	private byte numOfClasses = 1;
	/** current number of markers */
	private byte numOfMarkers = 0;
	/** current number of channels */
	private byte numOfChannels = 1;
	/** chosen channel for marker thresholding*/
	private byte chosenChannel = 0;
	
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
	/** button to filter nuclei */
	//private JButton filterNucleiButton;
	/** button to analyze each independent class */
	private JButton analyzeClassesButton;
	/** button to batch analyze each independent class */
	private JButton batchClassesMeasurementsButton;
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
	
	/** buttons to analyze each independent channel */
	/** add marker */
	private JButton addMarkerButton;
	/** batch */
	private JButton batchMarkerButton;
	
	/** radio buttons for selecting classes */
	private JRadioButton marker1Button;
	private JButton marker1ColorButton;
	private JButton marker1RemoveButton;
	private JRadioButton marker1Pattern1Button;
	private JRadioButton marker1Pattern2Button;
	private JRadioButton marker1Pattern3Button;
	private JRadioButton marker1Pattern4Button;
	private JRadioButton marker2Button;
	private JButton marker2ColorButton;
	private JButton marker2RemoveButton;
	private JRadioButton marker2Pattern1Button;
	private JRadioButton marker2Pattern2Button;
	private JRadioButton marker2Pattern3Button;
	private JRadioButton marker2Pattern4Button;
	private JRadioButton marker3Button;
	private JButton marker3ColorButton;
	private JButton marker3RemoveButton;
	private JRadioButton marker3Pattern1Button;
	private JRadioButton marker3Pattern2Button;
	private JRadioButton marker3Pattern3Button;
	private JRadioButton marker3Pattern4Button;
	private JRadioButton marker4Button;
	private JButton marker4ColorButton;
	private JButton marker4RemoveButton;
	private JRadioButton marker4Pattern1Button;
	private JRadioButton marker4Pattern2Button;
	private JRadioButton marker4Pattern3Button;
	private JRadioButton marker4Pattern4Button;
	private JRadioButton marker5Button;
	private JButton marker5ColorButton;
	private JButton marker5RemoveButton;
	private JRadioButton marker5Pattern1Button;
	private JRadioButton marker5Pattern2Button;
	private JRadioButton marker5Pattern3Button;
	private JRadioButton marker5Pattern4Button;
	private JRadioButton marker6Button;
	private JButton marker6ColorButton;
	private JButton marker6RemoveButton;
	private JRadioButton marker6Pattern1Button;
	private JRadioButton marker6Pattern2Button;
	private JRadioButton marker6Pattern3Button;
	private JRadioButton marker6Pattern4Button;
	private JRadioButton marker7Button;
	private JButton marker7ColorButton;
	private JButton marker7RemoveButton;
	private JRadioButton marker7Pattern1Button;
	private JRadioButton marker7Pattern2Button;
	private JRadioButton marker7Pattern3Button;
	private JRadioButton marker7Pattern4Button;
	
	/** buttons to analyze nuclei markers */
	private JButton analyzeMarkerButton;
	/** button to batch analyze nuclei markers  */
	private JButton batchMarkerMeasurementsButton;
	/** button to visualize image with overlays for figure/presentation */
	private JButton markerSnapshotButton;
	
	/** buttons to load and save segmentations */
	private JButton loadButton1;
	private JButton saveButton1;
	private JButton loadButton2;
	private JButton saveButton2;
	
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
	
	/** slider bars for marker thresholding */
	private JSlider intensityThresholdingScrollBar;
	private JTextArea intensityThresholdingTextArea;
	private JButton setIntensityThresholdButton;
	private JSlider areaThresholdingScrollBar;
	private JTextArea areaThresholdingTextArea;
	private JButton setAreaThresholdButton;
	/** ok and cancel buttons for thresholding */
	private JButton okMarkerButton;
	private JButton cancelMarkerButton;
	/** variable used for marker thresholds */
	short[][] intensityThresholds;
	/** folder for batch processing */
	private String imageFolder = new String();
	private String segmentationFolder = new String();
	private String markerFolder = new String();
	private String measurementsFolder = new String();
	
	
	/**
	 * Basic constructor
	 */
	public Annotater() 
	{
		nucleiAnnotationButton = new JRadioButton("Nuclei annotation");
		nucleiMarkerButton = new JRadioButton("Nuclei marker");

		newObjectButton = new JRadioButton("Annotate new objects");
		newObjectButton.setToolTipText("Each ROI creates a new object");

		removeObjectButton = new JRadioButton("Remove objects");
		removeObjectButton.setToolTipText("Remove object");		

		mergeObjectsButton = new JRadioButton("Merge objects");
		mergeObjectsButton.setToolTipText("Consecutively clicked objects are merged");
		
		splitObjectsButton = new JRadioButton("Split objects");
		splitObjectsButton.setToolTipText("Draw ROI inside an object to split it into two");
		
		swapObjectClassButton = new JRadioButton("Swap object class");
		swapObjectClassButton.setToolTipText("Swap object class");

		addClassButton = new JButton("Add new class");
		class1Button = new JRadioButton("Class 1");
		class2Button = new JRadioButton("Class 2");
		class3Button = new JRadioButton("Class 3");
		class4Button = new JRadioButton("Class 4");
		class5Button = new JRadioButton("Class 5");

		class1ColorButton = new JButton("Color");
		class2ColorButton = new JButton("Color");
		class3ColorButton = new JButton("Color");
		class4ColorButton = new JButton("Color");
		class5ColorButton = new JButton("Color");
		
		class1RemoveButton = new JButton("Remove");
		class2RemoveButton = new JButton("Remove");
		class3RemoveButton = new JButton("Remove");
		class4RemoveButton = new JButton("Remove");
		class5RemoveButton = new JButton("Remove");
		
		//filterNucleiButton = new JButton("Filter nuclei");
		analyzeClassesButton = new JButton("Measurements");
		batchClassesMeasurementsButton = new JButton("Batch");
		classSnapshotButton = new JButton("Snapshot");
		
		visualizeChannel1onlyButton1 = new JRadioButton("Channel1 only");
		visualizeChannel2onlyButton1 = new JRadioButton("Channel2 only");
		visualizeChannel3onlyButton1 = new JRadioButton("Channel3 only");
		visualizeChannel4onlyButton1 = new JRadioButton("Channel4 only");
		visualizeChannel5onlyButton1 = new JRadioButton("Channel5 only");
		visualizeChannel6onlyButton1 = new JRadioButton("Channel6 only");
		visualizeChannel7onlyButton1 = new JRadioButton("Channel7 only");
		visualizeChannel1Button1 = new JRadioButton("Channel1");
		visualizeChannel2Button1 = new JRadioButton("Channel2");
		visualizeChannel3Button1 = new JRadioButton("Channel3");
		visualizeChannel4Button1 = new JRadioButton("Channel4");
		visualizeChannel5Button1 = new JRadioButton("Channel5");
		visualizeChannel6Button1 = new JRadioButton("Channel6");
		visualizeChannel7Button1 = new JRadioButton("Channel7");
		visualizeAllChannelsButton1 = new JRadioButton("All channels");
		visualizeChannel1onlyButton2 = new JRadioButton("Channel1 only");
		visualizeChannel2onlyButton2 = new JRadioButton("Channel2 only");
		visualizeChannel3onlyButton2 = new JRadioButton("Channel3 only");
		visualizeChannel4onlyButton2 = new JRadioButton("Channel4 only");
		visualizeChannel5onlyButton2 = new JRadioButton("Channel5 only");
		visualizeChannel6onlyButton2 = new JRadioButton("Channel6 only");
		visualizeChannel7onlyButton2 = new JRadioButton("Channel7 only");
		visualizeChannel1Button2 = new JRadioButton("Channel1");
		visualizeChannel2Button2 = new JRadioButton("Channel2");
		visualizeChannel3Button2 = new JRadioButton("Channel3");
		visualizeChannel4Button2 = new JRadioButton("Channel4");
		visualizeChannel5Button2 = new JRadioButton("Channel5");
		visualizeChannel6Button2 = new JRadioButton("Channel6");
		visualizeChannel7Button2 = new JRadioButton("Channel7");
		visualizeAllChannelsButton2 = new JRadioButton("All channels");
		
		addMarkerButton = new JButton("Add new marker");
		batchMarkerButton = new JButton("Batch");
		marker1Button = new JRadioButton("Marker1");
		marker1ColorButton = new JButton("Color");
		marker1RemoveButton = new JButton("Remove");
		marker1Pattern1Button = new JRadioButton("P1");
		marker1Pattern2Button = new JRadioButton("P2");
		marker1Pattern3Button = new JRadioButton("P3");
		marker1Pattern4Button = new JRadioButton("P4");
		marker2Button = new JRadioButton("Marker2");
		marker2ColorButton = new JButton("Color");
		marker2RemoveButton = new JButton("Remove");
		marker2Pattern1Button = new JRadioButton("P1");
		marker2Pattern2Button = new JRadioButton("P2");
		marker2Pattern3Button = new JRadioButton("P3");
		marker2Pattern4Button = new JRadioButton("P4");
		marker3Button = new JRadioButton("Marker3");
		marker3ColorButton = new JButton("Color");
		marker3RemoveButton = new JButton("Remove");
		marker3Pattern1Button = new JRadioButton("P1");
		marker3Pattern2Button = new JRadioButton("P2");
		marker3Pattern3Button = new JRadioButton("P3");
		marker3Pattern4Button = new JRadioButton("P4");
		marker4Button = new JRadioButton("Marker4");
		marker4ColorButton = new JButton("Color");
		marker4RemoveButton = new JButton("Remove");
		marker4Pattern1Button = new JRadioButton("P1");
		marker4Pattern2Button = new JRadioButton("P2");
		marker4Pattern3Button = new JRadioButton("P3");
		marker4Pattern4Button = new JRadioButton("P4");
		marker5Button = new JRadioButton("Marker5");
		marker5ColorButton = new JButton("Color");
		marker5RemoveButton = new JButton("Remove");
		marker5Pattern1Button = new JRadioButton("P1");
		marker5Pattern2Button = new JRadioButton("P2");
		marker5Pattern3Button = new JRadioButton("P3");
		marker5Pattern4Button = new JRadioButton("P4");
		marker6Button = new JRadioButton("Marker6");
		marker6ColorButton = new JButton("Color");
		marker6RemoveButton = new JButton("Remove");
		marker6Pattern1Button = new JRadioButton("P1");
		marker6Pattern2Button = new JRadioButton("P2");
		marker6Pattern3Button = new JRadioButton("P3");
		marker6Pattern4Button = new JRadioButton("P4");
		marker7Button = new JRadioButton("Marker7");
		marker7ColorButton = new JButton("Color");
		marker7RemoveButton = new JButton("Remove");
		marker7Pattern1Button = new JRadioButton("P1");
		marker7Pattern2Button = new JRadioButton("P2");
		marker7Pattern3Button = new JRadioButton("P3");
		marker7Pattern4Button = new JRadioButton("P4");
		
		analyzeMarkerButton = new JButton("Measurements");
		batchMarkerMeasurementsButton = new JButton("Batch");
		markerSnapshotButton = new JButton("Snapshot");
		loadButton1 = new JButton("Load");
		saveButton1 = new JButton("Save");
		loadButton2 = new JButton("Load");
		saveButton2 = new JButton("Save");
		
		overlay = new Overlay();
		markersOverlay = new Overlay();
		roiListener = new RoiListener();
		keyListener = new KeyActions();
		
		objectsInEachClass[0] = new ArrayList<Point[]>();
		firstObjectToMerge_class = -1;firstObjectToMerge_classId = -1;firstObjectToMerge_overlayId = -1;
		
		for(int j = 0; j < 4; j++) {
			positiveNucleiForEachMarker[0][j] = new ArrayList<Short>();
		}
	
		redCheck = new JRadioButton("Red");
		greenCheck = new JRadioButton("Green");
		blueCheck = new JRadioButton("Blue");
		yellowCheck = new JRadioButton("Yellow");
		magentaCheck = new JRadioButton("Magenta");
		cyanCheck = new JRadioButton("Cyan");
		orangeCheck = new JRadioButton("Orange");
		pinkCheck = new JRadioButton("Pink");
		blackCheck = new JRadioButton("Black");
		grayCheck = new JRadioButton("Gray");
		whiteCheck = new JRadioButton("White");
		
		redCheck1 = new JRadioButton("Red");
		greenCheck1 = new JRadioButton("Green");
		blueCheck1 = new JRadioButton("Blue");
		yellowCheck1 = new JRadioButton("Yellow");
		magentaCheck1 = new JRadioButton("Magenta");
		cyanCheck1 = new JRadioButton("Cyan");
		orangeCheck1 = new JRadioButton("Orange");
		pinkCheck1 = new JRadioButton("Pink");
		blackCheck1 = new JRadioButton("Black");
		grayCheck1 = new JRadioButton("Gray");
		whiteCheck1 = new JRadioButton("White");
		redCheck2 = new JRadioButton("Red");
		greenCheck2 = new JRadioButton("Green");
		blueCheck2 = new JRadioButton("Blue");
		yellowCheck2 = new JRadioButton("Yellow");
		magentaCheck2 = new JRadioButton("Magenta");
		cyanCheck2 = new JRadioButton("Cyan");
		orangeCheck2 = new JRadioButton("Orange");
		pinkCheck2 = new JRadioButton("Pink");
		blackCheck2 = new JRadioButton("Black");
		grayCheck2 = new JRadioButton("Gray");
		whiteCheck2 = new JRadioButton("White");
		redCheck3 = new JRadioButton("Red");
		greenCheck3 = new JRadioButton("Green");
		blueCheck3 = new JRadioButton("Blue");
		yellowCheck3 = new JRadioButton("Yellow");
		magentaCheck3 = new JRadioButton("Magenta");
		cyanCheck3 = new JRadioButton("Cyan");
		orangeCheck3 = new JRadioButton("Orange");
		pinkCheck3 = new JRadioButton("Pink");
		blackCheck3 = new JRadioButton("Black");
		grayCheck3 = new JRadioButton("Gray");
		whiteCheck3 = new JRadioButton("White");
		redCheck4 = new JRadioButton("Red");
		greenCheck4 = new JRadioButton("Green");
		blueCheck4 = new JRadioButton("Blue");
		yellowCheck4 = new JRadioButton("Yellow");
		magentaCheck4 = new JRadioButton("Magenta");
		cyanCheck4 = new JRadioButton("Cyan");
		orangeCheck4 = new JRadioButton("Orange");
		pinkCheck4 = new JRadioButton("Pink");
		blackCheck4 = new JRadioButton("Black");
		grayCheck4 = new JRadioButton("Gray");
		whiteCheck4 = new JRadioButton("White");
		
		intensityThresholdingScrollBar = new JSlider(0, 100, 0);
		intensityThresholdingTextArea = new JTextArea();
		setIntensityThresholdButton = new JButton("Set threshold");
		areaThresholdingScrollBar = new JSlider(0, 100, 35);
		areaThresholdingTextArea = new JTextArea();
		setAreaThresholdButton = new JButton("Set threshold");
		okMarkerButton = new JButton("Ok");
		cancelMarkerButton = new JButton("Cancel");
	}
	
	@Override
	public void run() {

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
			//originalLUT = displayImage.getLuts();
			
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
			
			//Build GUI
			SwingUtilities.invokeLater(
					new Runnable() {
						public void run() {
							win = new CustomWindow(displayImage);
							win.pack();
						}
					});
			
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
			//originalLUT = displayImage.getLuts();

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

			//Build GUI
			SwingUtilities.invokeLater(
					new Runnable() {
						public void run() {
							win = new CustomWindow(displayImage);
							win.pack();
						}
					});
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
	void updateRoiColor(int consideredClass) {
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
		else {
			classColors[consideredClass] = selectedColor;
			updateClassColor();
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
			if(colorPattern1!=markerColors[consideredMarker][0]) {markerColors[consideredMarker][0] = colorPattern1;change=true;}
			if(colorPattern2!=markerColors[consideredMarker][1]) {markerColors[consideredMarker][1] = colorPattern2;change=true;}
			if(colorPattern3!=markerColors[consideredMarker][2]) {markerColors[consideredMarker][2] = colorPattern3;change=true;}
			if(colorPattern4!=markerColors[consideredMarker][3]) {markerColors[consideredMarker][3] = colorPattern4;change=true;}
			if(change) {
				removeCurrentNucleiMarkerOverlays();
				activateCurrentNucleiMarkerOverlays(consideredMarker);
			}
		}
	}
	/** get image with classes as overlays for figures/presentations */
	void takeClassSnapshot() {
		ImageStack stack = displayImage.getStack();
		ImagePlus currentImage = new ImagePlus("Snapshot", stack) ;
		ImagePlus flattenedImage = HyperStackConverter.toHyperStack(currentImage, numOfChannels, 1, 1);
		LUT[] displayImageLUT = displayImage.getLuts();
		for(int c=0;c<displayImage.getNChannels();c++) {
			flattenedImage.setPosition(c+1, flattenedImage.getSlice(), flattenedImage.getFrame());
			flattenedImage.setDisplayRange(displayImageLUT[c].min, displayImageLUT[c].max);
		}						
		if(overlay.size()>0) {flattenedImage.setOverlay(overlay);}
		flattenedImage.updateAndDraw();
		flattenedImage.show();
		IJ.run("Flatten");
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
					if(e.getSource() == nucleiAnnotationButton){
						updateModeRadioButtons(0);
					}
					else if(e.getSource() == nucleiMarkerButton){
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
						boolean ok = updateRoiColorWindow(0);
						if(ok) {updateRoiColor(0);}							
					}
					else if(e.getSource() == class1RemoveButton){
						removeClass(0);
					}
					else if(e.getSource() == class2ColorButton){
						boolean ok = updateRoiColorWindow(1);
						if(ok) {updateRoiColor(1);}
					}
					else if(e.getSource() == class2RemoveButton){
						removeClass(1);
					}
					else if(e.getSource() == class3ColorButton){
						boolean ok = updateRoiColorWindow(2);
						if(ok) {updateRoiColor(2);}
					}
					else if(e.getSource() == class3RemoveButton){
						removeClass(2);
					}
					else if(e.getSource() == class4ColorButton){
						boolean ok = updateRoiColorWindow(3);
						if(ok) {updateRoiColor(3);}
					}
					else if(e.getSource() == class4RemoveButton){
						removeClass(3);
					}
					else if(e.getSource() == class5ColorButton){
						boolean ok = updateRoiColorWindow(4);
						if(ok) {updateRoiColor(4);}
					}
					else if(e.getSource() == class5RemoveButton){
						removeClass(4);
					}
					else if(e.getSource() == analyzeClassesButton){
						classMeasurements();
					}
					/*else if(e.getSource() == filterNucleiButton){
						addFilterWindow();
					}*/
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
					else if(e.getSource() == addMarkerButton){
						if(objectsInEachClass[0].size()==0) {
							IJ.showMessage("Define nuclei before identifying markers associated with the nuclei");
						}
						else {
							initializeMarkerButtons();
							removeMarkersFromOverlay();
							boolean okNbMarkers = addNewMarker();
							if(okNbMarkers) {
								boolean ok = addMarkerWindow();
								if(!ok) {deleteMarker(numOfMarkers-1);}
								else {updateAnnotateMarker(numOfMarkers-1);}
							}
						}
					}
					else if(e.getSource() == setIntensityThresholdButton){
						addIntensityThresholdingWindow();
					}
					else if(e.getSource() == setAreaThresholdButton){
						addAreaThresholdingWindow();
					}
					else if(e.getSource() == okMarkerButton){
						updateModeRadioButtons(1);
						updateAnnotateMarker(numOfMarkers-1);
						okMarkerButton.removeActionListener(listener);
						cancelMarkerButton.removeActionListener(listener);
						setIntensityThresholdButton.removeActionListener(listener);
						setAreaThresholdButton.removeActionListener(listener);
						for( ChangeListener al : intensityThresholdingScrollBar.getChangeListeners() ) {intensityThresholdingScrollBar.removeChangeListener( al );}
						for( ChangeListener al : areaThresholdingScrollBar.getChangeListeners() ) {areaThresholdingScrollBar.removeChangeListener( al );}
					}
					else if(e.getSource() == cancelMarkerButton){
						currentMode = 1;
						deleteMarker(numOfMarkers-1);
						okMarkerButton.removeActionListener(listener);
						cancelMarkerButton.removeActionListener(listener);
						setIntensityThresholdButton.removeActionListener(listener);
						setAreaThresholdButton.removeActionListener(listener);
						for( ChangeListener al : intensityThresholdingScrollBar.getChangeListeners() ) {intensityThresholdingScrollBar.removeChangeListener( al );}
						for( ChangeListener al : areaThresholdingScrollBar.getChangeListeners() ) {areaThresholdingScrollBar.removeChangeListener( al );}
					}
					else if(e.getSource() == batchMarkerButton) {
						batchMarker();
					}
					else if(e.getSource() == batchClassesMeasurementsButton) {
						batchMeasurements(0);
					}
					else if(e.getSource() == batchMarkerMeasurementsButton) {
						batchMeasurements(1);
					}
					else if(e.getSource() == marker1Button){
						updateAnnotateMarker(0);
					}
					else if(e.getSource() == marker2Button){
						updateAnnotateMarker(1);
					}
					else if(e.getSource() == marker3Button){
						updateAnnotateMarker(2);
					}
					else if(e.getSource() == marker4Button){
						updateAnnotateMarker(3);
					}
					else if(e.getSource() == marker5Button){
						updateAnnotateMarker(4);
					}
					else if(e.getSource() == marker6Button){
						updateAnnotateMarker(5);
					}
					else if(e.getSource() == marker7Button){
						updateAnnotateMarker(6);
					}
					else if(e.getSource() == marker1ColorButton){
						boolean ok = updatePatternColorsWindow(0);
						if(ok) {updatePatternColor(0);}
					}
					else if(e.getSource() == marker1RemoveButton){
						removeMarker(0);
					}
					else if(e.getSource() == marker2ColorButton){
						boolean ok = updatePatternColorsWindow(1);
						if(ok) {updatePatternColor(1);}
					}
					else if(e.getSource() == marker2RemoveButton){
						removeMarker(1);
					}
					else if(e.getSource() == marker3ColorButton){
						boolean ok = updatePatternColorsWindow(2);
						if(ok) {updatePatternColor(2);}
					}
					else if(e.getSource() == marker3RemoveButton){
						removeMarker(2);
					}
					else if(e.getSource() == marker4ColorButton){
						boolean ok = updatePatternColorsWindow(3);
						if(ok) {updatePatternColor(3);}
					}
					else if(e.getSource() == marker4RemoveButton){
						removeMarker(3);
					}
					else if(e.getSource() == marker5ColorButton){
						boolean ok = updatePatternColorsWindow(4);
						if(ok) {updatePatternColor(4);}
					}
					else if(e.getSource() == marker5RemoveButton){
						removeMarker(4);
					}
					else if(e.getSource() == marker6ColorButton){
						boolean ok = updatePatternColorsWindow(5);
						if(ok) {updatePatternColor(5);}
					}
					else if(e.getSource() == marker6RemoveButton){
						removeMarker(5);
					}
					else if(e.getSource() == marker7ColorButton){
						boolean ok = updatePatternColorsWindow(6);
						if(ok) {updatePatternColor(6);}
					}
					else if(e.getSource() == marker7RemoveButton){
						removeMarker(6);
					}
					else if(e.getSource() == marker1Pattern1Button){
						updateAnnotateChannelPatternButtons(0);
					}
					else if(e.getSource() == marker1Pattern2Button){
						updateAnnotateChannelPatternButtons(1);
					}
					else if(e.getSource() == marker1Pattern3Button){
						updateAnnotateChannelPatternButtons(2);
					}
					else if(e.getSource() == marker1Pattern4Button){
						updateAnnotateChannelPatternButtons(3);
					}
					else if(e.getSource() == marker2Pattern1Button){
						updateAnnotateChannelPatternButtons(4);
					}
					else if(e.getSource() == marker2Pattern2Button){
						updateAnnotateChannelPatternButtons(5);
					}
					else if(e.getSource() == marker2Pattern3Button){
						updateAnnotateChannelPatternButtons(6);
					}
					else if(e.getSource() == marker2Pattern4Button){
						updateAnnotateChannelPatternButtons(7);
					}
					else if(e.getSource() == marker3Pattern1Button){
						updateAnnotateChannelPatternButtons(8);
					}
					else if(e.getSource() == marker3Pattern2Button){
						updateAnnotateChannelPatternButtons(9);
					}
					else if(e.getSource() == marker3Pattern3Button){
						updateAnnotateChannelPatternButtons(10);
					}
					else if(e.getSource() == marker3Pattern4Button){
						updateAnnotateChannelPatternButtons(11);
					}
					else if(e.getSource() == marker4Pattern1Button){
						updateAnnotateChannelPatternButtons(12);
					}
					else if(e.getSource() == marker4Pattern2Button){
						updateAnnotateChannelPatternButtons(13);
					}
					else if(e.getSource() == marker4Pattern3Button){
						updateAnnotateChannelPatternButtons(14);
					}
					else if(e.getSource() == marker4Pattern4Button){
						updateAnnotateChannelPatternButtons(15);
					}
					else if(e.getSource() == marker5Pattern1Button){
						updateAnnotateChannelPatternButtons(16);
					}
					else if(e.getSource() == marker5Pattern2Button){
						updateAnnotateChannelPatternButtons(17);
					}
					else if(e.getSource() == marker5Pattern3Button){
						updateAnnotateChannelPatternButtons(18);
					}
					else if(e.getSource() == marker5Pattern4Button){
						updateAnnotateChannelPatternButtons(19);
					}
					else if(e.getSource() == marker6Pattern1Button){
						updateAnnotateChannelPatternButtons(20);
					}
					else if(e.getSource() == marker6Pattern2Button){
						updateAnnotateChannelPatternButtons(21);
					}
					else if(e.getSource() == marker6Pattern3Button){
						updateAnnotateChannelPatternButtons(22);
					}
					else if(e.getSource() == marker6Pattern4Button){
						updateAnnotateChannelPatternButtons(23);
					}
					else if(e.getSource() == marker7Pattern1Button){
						updateAnnotateChannelPatternButtons(24);
					}
					else if(e.getSource() == marker7Pattern2Button){
						updateAnnotateChannelPatternButtons(25);
					}
					else if(e.getSource() == marker7Pattern3Button){
						updateAnnotateChannelPatternButtons(26);
					}
					else if(e.getSource() == marker7Pattern4Button){
						updateAnnotateChannelPatternButtons(27);
					}
					else if(e.getSource() == analyzeMarkerButton){
						markerMeasurements();
					}
					else if(e.getSource() == markerSnapshotButton){
						takeMarkerSnapshot();
					}
					else if(e.getSource() == loadButton1){
						loadNucleiSegmentations();
					}
					else if(e.getSource() == saveButton1){
						saveNucleiSegmentation();
					}
					else if(e.getSource() == loadButton2){
						loadMarkerIdentifications();
					}
					else if(e.getSource() == saveButton2){
						saveNucleiIdentification();
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
		public void mouseExited(MouseEvent e) {
		}

		@Override
		public void mousePressed(MouseEvent e) {}

		@Override
		public void mouseReleased( final MouseEvent e )
		{
			if(!mousePanning) {
				Roi roi = displayImage.getRoi();
				if (roi != null && roi.getType() == Roi.FREEROI && currentMode == 0) {
					if(newObjectButton.isSelected()) {addObject();}
				}
				if (roi != null && roi.getType() == Roi.POINT && currentMode == 0) {
					if(mergeObjectsButton.isSelected()) {mergeObjects();}
					if(removeObjectButton.isSelected()) {removeObject();}//classMeasurementsForOneNucleus();}
					if(swapObjectClassButton.isSelected()) {swapObjectClass();}
				}
				if (roi != null && roi.getType() == Roi.POINT && currentMode == 1) {
					annotateNucleusMarker();
				}
				if (roi != null && roi.getType() == Roi.FREELINE && currentMode == 0) {
					if(splitObjectsButton.isSelected()) {splitObject();}
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
			case 32:
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
			case 32:
				if(!mousePanning) {mousePanning = true;Toolbar.getInstance().setTool(Toolbar.HAND);}
				break;
				
			case 37:
				navigateLeft(displayImage);
				break;

			case 38:
				navigateUp(displayImage);
				break;

			case 39:
				navigateRight(displayImage);
				break;

			case 40:
				navigateDown(displayImage);
				break;

			case 107:
				IJ.run("In [+]");
				break;

			case 109:
				IJ.run("Out [-]");
				break;

			case 61:
				IJ.run("In [+]");
				break;

			case 45:
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
		marker1Button.removeActionListener(listener);
		marker1ColorButton.removeActionListener(listener);
		marker1RemoveButton.removeActionListener(listener);
		marker1Pattern1Button.removeActionListener(listener);
		marker1Pattern2Button.removeActionListener(listener);
		marker1Pattern3Button.removeActionListener(listener);
		marker1Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker2ButtonFromListener() {
		marker2Button.removeActionListener(listener);
		marker2ColorButton.removeActionListener(listener);
		marker2RemoveButton.removeActionListener(listener);
		marker2Pattern1Button.removeActionListener(listener);
		marker2Pattern2Button.removeActionListener(listener);
		marker2Pattern3Button.removeActionListener(listener);
		marker2Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker3ButtonFromListener() {
		marker3Button.removeActionListener(listener);
		marker3ColorButton.removeActionListener(listener);
		marker3RemoveButton.removeActionListener(listener);
		marker3Pattern1Button.removeActionListener(listener);
		marker3Pattern2Button.removeActionListener(listener);
		marker3Pattern3Button.removeActionListener(listener);
		marker3Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker4ButtonFromListener() {
		marker4Button.removeActionListener(listener);
		marker4ColorButton.removeActionListener(listener);
		marker4RemoveButton.removeActionListener(listener);
		marker4Pattern1Button.removeActionListener(listener);
		marker4Pattern2Button.removeActionListener(listener);
		marker4Pattern3Button.removeActionListener(listener);
		marker4Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker5ButtonFromListener() {
		marker5Button.removeActionListener(listener);
		marker5ColorButton.removeActionListener(listener);
		marker5RemoveButton.removeActionListener(listener);
		marker5Pattern1Button.removeActionListener(listener);
		marker5Pattern2Button.removeActionListener(listener);
		marker5Pattern3Button.removeActionListener(listener);
		marker5Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker6ButtonFromListener() {
		marker6Button.removeActionListener(listener);
		marker6ColorButton.removeActionListener(listener);
		marker6RemoveButton.removeActionListener(listener);
		marker6Pattern1Button.removeActionListener(listener);
		marker6Pattern2Button.removeActionListener(listener);
		marker6Pattern3Button.removeActionListener(listener);
		marker6Pattern4Button.removeActionListener(listener);
	}
	public void removeMarker7ButtonFromListener() {
		marker7Button.removeActionListener(listener);
		marker7ColorButton.removeActionListener(listener);
		marker7RemoveButton.removeActionListener(listener);
		marker7Pattern1Button.removeActionListener(listener);
		marker7Pattern2Button.removeActionListener(listener);
		marker7Pattern3Button.removeActionListener(listener);
		marker7Pattern4Button.removeActionListener(listener);
	}
	/**
	 * Functions to remove marker associated buttons
	 */
	public void addMarker1ButtonFromListener() {
		marker1Button.addActionListener(listener);
		marker1ColorButton.addActionListener(listener);
		marker1RemoveButton.addActionListener(listener);
		marker1Pattern1Button.addActionListener(listener);
		marker1Pattern2Button.addActionListener(listener);
		marker1Pattern3Button.addActionListener(listener);
		marker1Pattern4Button.addActionListener(listener);
	}
	public void addMarker2ButtonFromListener() {
		marker2Button.addActionListener(listener);
		marker2ColorButton.addActionListener(listener);
		marker2RemoveButton.addActionListener(listener);
		marker2Pattern1Button.addActionListener(listener);
		marker2Pattern2Button.addActionListener(listener);
		marker2Pattern3Button.addActionListener(listener);
		marker2Pattern4Button.addActionListener(listener);
	}
	public void addMarker3ButtonFromListener() {
		marker3Button.addActionListener(listener);
		marker3ColorButton.addActionListener(listener);
		marker3RemoveButton.addActionListener(listener);
		marker3Pattern1Button.addActionListener(listener);
		marker3Pattern2Button.addActionListener(listener);
		marker3Pattern3Button.addActionListener(listener);
		marker3Pattern4Button.addActionListener(listener);
	}
	public void addMarker4ButtonFromListener() {
		marker4Button.addActionListener(listener);
		marker4ColorButton.addActionListener(listener);
		marker4RemoveButton.addActionListener(listener);
		marker4Pattern1Button.addActionListener(listener);
		marker4Pattern2Button.addActionListener(listener);
		marker4Pattern3Button.addActionListener(listener);
		marker4Pattern4Button.addActionListener(listener);
	}
	public void addMarker5ButtonFromListener() {
		marker5Button.addActionListener(listener);
		marker5ColorButton.addActionListener(listener);
		marker5RemoveButton.addActionListener(listener);
		marker5Pattern1Button.addActionListener(listener);
		marker5Pattern2Button.addActionListener(listener);
		marker5Pattern3Button.addActionListener(listener);
		marker5Pattern4Button.addActionListener(listener);
	}
	public void addMarker6ButtonFromListener() {
		marker6Button.addActionListener(listener);
		marker6ColorButton.addActionListener(listener);
		marker6RemoveButton.addActionListener(listener);
		marker6Pattern1Button.addActionListener(listener);
		marker6Pattern2Button.addActionListener(listener);
		marker6Pattern3Button.addActionListener(listener);
		marker6Pattern4Button.addActionListener(listener);
	}
	public void addMarker7ButtonFromListener() {
		marker7Button.addActionListener(listener);
		marker7ColorButton.addActionListener(listener);
		marker7RemoveButton.addActionListener(listener);
		marker7Pattern1Button.addActionListener(listener);
		marker7Pattern2Button.addActionListener(listener);
		marker7Pattern3Button.addActionListener(listener);
		marker7Pattern4Button.addActionListener(listener);
	}
	/**
	 * Custom window to define the GUI
	 */
	private class CustomWindow extends ImageWindow 
	{
		private JPanel modePanel = new JPanel();
		private JPanel analysisPanel1 = new JPanel();
		private JPanel analysisPanel2 = new JPanel();
		private JPanel annotationPanel = new JPanel();
		private JPanel classesPanel = new JPanel();
		private JPanel class1Panel = new JPanel();
		private JPanel class2Panel = new JPanel();
		private JPanel class3Panel = new JPanel();
		private JPanel class4Panel = new JPanel();
		private JPanel class5Panel = new JPanel();
		private JPanel markerPanel = new JPanel();
		private JPanel marker1PatternPanel1 = new JPanel();
		private JPanel marker1PatternPanel2 = new JPanel();
		private JPanel marker2PatternPanel1 = new JPanel();
		private JPanel marker2PatternPanel2 = new JPanel();
		private JPanel marker3PatternPanel1 = new JPanel();
		private JPanel marker3PatternPanel2 = new JPanel();
		private JPanel marker4PatternPanel1 = new JPanel();
		private JPanel marker4PatternPanel2 = new JPanel();
		private JPanel marker5PatternPanel1 = new JPanel();
		private JPanel marker5PatternPanel2 = new JPanel();
		private JPanel marker6PatternPanel1 = new JPanel();
		private JPanel marker6PatternPanel2 = new JPanel();
		private JPanel marker7PatternPanel1 = new JPanel();
		private JPanel marker7PatternPanel2 = new JPanel();
		private JPanel visualizationPanel1 = new JPanel();
		private JPanel visualizationPanel2 = new JPanel();
		private JPanel filePanel1 = new JPanel();
		private JPanel filePanel2 = new JPanel();
		
		private JPanel topPanel = new JPanel();
		private JPanel leftPanel1 = new JPanel();
		private JPanel rightPanel1 = new JPanel();
		private JPanel leftPanel2 = new JPanel();
		private JPanel rightPanel2 = new JPanel();
		private JPanel bottomPanel = new JPanel();
		
		private Panel all = new Panel();

		GridBagLayout classesLayout = new GridBagLayout();
		GridBagConstraints classesConstraints = new GridBagConstraints();
		GridBagLayout markerLayout = new GridBagLayout();
		GridBagConstraints markerConstraints = new GridBagConstraints();
		GridBagLayout analysisLayout1 = new GridBagLayout();
		GridBagConstraints analysisContraints1 = new GridBagConstraints();
		
		CustomWindow(ImagePlus imp) 
		{
			super(imp, new CustomCanvas(imp));

			final CustomCanvas canvas = (CustomCanvas) getCanvas();

			// Remove the canvas from the window, to add it later
			removeAll();

			setTitle("Annotater");

			// Mode panel
			modePanel.setBorder(BorderFactory.createTitledBorder("Mode"));
			GridBagLayout modeLayout = new GridBagLayout();
			GridBagConstraints modeConstraints = new GridBagConstraints();
			modeConstraints.anchor = GridBagConstraints.NORTHWEST;
			modeConstraints.fill = GridBagConstraints.HORIZONTAL;
			modeConstraints.gridwidth = 1;
			modeConstraints.gridheight = 1;
			modeConstraints.gridx = 0;
			modeConstraints.gridy = 0;
			modePanel.setLayout(modeLayout);
			
			modePanel.add(nucleiAnnotationButton,modeConstraints);
			modeConstraints.gridx++;
			modePanel.add(nucleiMarkerButton,modeConstraints);
			modeConstraints.gridx++;
			if(currentMode==0) {
				nucleiAnnotationButton.setSelected(true);
				nucleiMarkerButton.setSelected(false);
			}
			else {
				nucleiAnnotationButton.setSelected(false);
				nucleiMarkerButton.setSelected(true);
			}
			
			// File panel 1
			filePanel1.setBorder(BorderFactory.createTitledBorder("File"));
			GridBagLayout fileLayout1 = new GridBagLayout();
			GridBagConstraints fileConstraints1 = new GridBagConstraints();
			fileConstraints1.anchor = GridBagConstraints.NORTHWEST;
			fileConstraints1.fill = GridBagConstraints.HORIZONTAL;
			fileConstraints1.gridwidth = 1;
			fileConstraints1.gridheight = 1;
			fileConstraints1.gridx = 0;
			fileConstraints1.gridy = 0;
			filePanel1.setLayout(fileLayout1);
						
			filePanel1.add(loadButton1,fileConstraints1);
			fileConstraints1.gridy++;
			filePanel1.add(saveButton1,fileConstraints1);
			fileConstraints1.gridy++;
			
			// File panel 2
			filePanel2.setBorder(BorderFactory.createTitledBorder("File"));
			GridBagLayout fileLayout2 = new GridBagLayout();
			GridBagConstraints fileConstraints2 = new GridBagConstraints();
			fileConstraints2.anchor = GridBagConstraints.NORTHWEST;
			fileConstraints2.fill = GridBagConstraints.HORIZONTAL;
			fileConstraints2.gridwidth = 1;
			fileConstraints2.gridheight = 1;
			fileConstraints2.gridx = 0;
			fileConstraints2.gridy = 0;
			filePanel2.setLayout(fileLayout2);

			filePanel2.add(loadButton2,fileConstraints2);
			fileConstraints2.gridy++;
			filePanel2.add(saveButton2,fileConstraints2);
			fileConstraints2.gridy++;
			
			// Analysis panel 1
			analysisPanel1.setBorder(BorderFactory.createTitledBorder("Analysis"));
			analysisContraints1.anchor = GridBagConstraints.NORTHWEST;
			analysisContraints1.fill = GridBagConstraints.HORIZONTAL;
			analysisContraints1.gridwidth = 1;
			analysisContraints1.gridheight = 1;
			analysisContraints1.gridx = 0;
			analysisContraints1.gridy = 0;
			analysisPanel1.setLayout(analysisLayout1);

			//analysisPanel1.add(filterNucleiButton,analysisContraints1);
			//analysisContraints1.gridy++;
			analysisPanel1.add(analyzeClassesButton,analysisContraints1);
			analysisContraints1.gridy++;
			analysisPanel1.add(batchClassesMeasurementsButton,analysisContraints1);
			analysisContraints1.gridy++;
			analysisPanel1.add(classSnapshotButton,analysisContraints1);
			analysisContraints1.gridy++;
			
			// Analysis panel 2
			analysisPanel2.setBorder(BorderFactory.createTitledBorder("Analysis"));
			GridBagLayout analysisLayout2 = new GridBagLayout();
			GridBagConstraints analysisConstraints2 = new GridBagConstraints();
			analysisConstraints2.anchor = GridBagConstraints.NORTHWEST;
			analysisConstraints2.fill = GridBagConstraints.HORIZONTAL;
			analysisConstraints2.gridwidth = 1;
			analysisConstraints2.gridheight = 1;
			analysisConstraints2.gridx = 0;
			analysisConstraints2.gridy = 0;
			analysisPanel2.setLayout(analysisLayout2);

			analysisPanel2.add(analyzeMarkerButton, analysisConstraints2);
			analysisConstraints2.gridy++;
			analysisPanel2.add(batchMarkerMeasurementsButton, analysisConstraints2);
			analysisConstraints2.gridy++;
			analysisPanel2.add(markerSnapshotButton,analysisConstraints2);
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
			marker1PatternPanel1.add(marker1Button);
			marker1PatternConstraints1.gridx++;
			marker1PatternPanel1.add(marker1ColorButton);
			marker1PatternConstraints1.gridx++;
			marker1PatternPanel1.add(marker1RemoveButton);

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

			marker1PatternPanel2.add(marker1Pattern1Button);
			marker1Pattern1Button.setSelected(false);
			marker1PatternConstraints2.gridx++;
			marker1PatternPanel2.add(marker1Pattern2Button);
			marker1Pattern2Button.setSelected(false);
			marker1PatternConstraints2.gridx++;
			marker1PatternPanel2.add(marker1Pattern3Button);
			marker1Pattern3Button.setSelected(false);
			marker1PatternConstraints2.gridx++;
			marker1PatternPanel2.add(marker1Pattern4Button);
			marker1Pattern4Button.setSelected(false);
			marker1PatternConstraints2.gridx++;

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
			marker2PatternPanel1.add(marker2Button);
			marker2PatternConstraints1.gridx++;
			marker2PatternPanel1.add(marker2ColorButton);
			marker2PatternConstraints1.gridx++;
			marker2PatternPanel1.add(marker2RemoveButton);

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

			marker2PatternPanel2.add(marker2Pattern1Button);
			marker2Pattern1Button.setSelected(false);
			marker2PatternConstraints2.gridx++;
			marker2PatternPanel2.add(marker2Pattern2Button);
			marker2Pattern2Button.setSelected(false);
			marker2PatternConstraints2.gridx++;
			marker2PatternPanel2.add(marker2Pattern3Button);
			marker2Pattern3Button.setSelected(false);
			marker2PatternConstraints2.gridx++;
			marker2PatternPanel2.add(marker2Pattern4Button);
			marker2Pattern4Button.setSelected(false);
			marker2PatternConstraints2.gridx++;

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
			marker3PatternPanel1.add(marker3Button);
			marker3PatternConstraints1.gridx++;
			marker3PatternPanel1.add(marker3ColorButton);
			marker3PatternConstraints1.gridx++;
			marker3PatternPanel1.add(marker3RemoveButton);

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

			marker3PatternPanel2.add(marker3Pattern1Button);
			marker3Pattern1Button.setSelected(false);
			marker3PatternConstraints2.gridx++;
			marker3PatternPanel2.add(marker3Pattern2Button);
			marker3Pattern2Button.setSelected(false);
			marker3PatternConstraints2.gridx++;
			marker3PatternPanel2.add(marker3Pattern3Button);
			marker3Pattern3Button.setSelected(false);
			marker3PatternConstraints2.gridx++;
			marker3PatternPanel2.add(marker3Pattern4Button);
			marker3Pattern4Button.setSelected(false);
			marker3PatternConstraints2.gridx++;

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
			marker4PatternPanel1.add(marker4Button);
			marker4PatternConstraints1.gridx++;
			marker4PatternPanel1.add(marker4ColorButton);
			marker4PatternConstraints1.gridx++;
			marker4PatternPanel1.add(marker4RemoveButton);

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

			marker4PatternPanel2.add(marker4Pattern1Button);
			marker4Pattern1Button.setSelected(false);
			marker4PatternConstraints2.gridx++;
			marker4PatternPanel2.add(marker4Pattern2Button);
			marker4Pattern2Button.setSelected(false);
			marker4PatternConstraints2.gridx++;
			marker4PatternPanel2.add(marker4Pattern3Button);
			marker4Pattern3Button.setSelected(false);
			marker4PatternConstraints2.gridx++;
			marker4PatternPanel2.add(marker4Pattern4Button);
			marker4Pattern4Button.setSelected(false);
			marker4PatternConstraints2.gridx++;

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
			marker5PatternPanel1.add(marker5Button);
			marker5PatternConstraints1.gridx++;
			marker5PatternPanel1.add(marker5ColorButton);
			marker5PatternConstraints1.gridx++;
			marker5PatternPanel1.add(marker5RemoveButton);

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

			marker5PatternPanel2.add(marker5Pattern1Button);
			marker5Pattern1Button.setSelected(false);
			marker5PatternConstraints2.gridx++;
			marker5PatternPanel2.add(marker5Pattern2Button);
			marker5Pattern2Button.setSelected(false);
			marker5PatternConstraints2.gridx++;
			marker5PatternPanel2.add(marker5Pattern3Button);
			marker5Pattern3Button.setSelected(false);
			marker5PatternConstraints2.gridx++;
			marker5PatternPanel2.add(marker5Pattern4Button);
			marker5Pattern4Button.setSelected(false);
			marker5PatternConstraints2.gridx++;

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
			marker6PatternPanel1.add(marker6Button);
			marker6PatternConstraints1.gridx++;
			marker6PatternPanel1.add(marker6ColorButton);
			marker6PatternConstraints1.gridx++;
			marker6PatternPanel1.add(marker6RemoveButton);

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

			marker6PatternPanel2.add(marker6Pattern1Button);
			marker6Pattern1Button.setSelected(false);
			marker6PatternConstraints2.gridx++;
			marker6PatternPanel2.add(marker6Pattern2Button);
			marker6Pattern2Button.setSelected(false);
			marker6PatternConstraints2.gridx++;
			marker6PatternPanel2.add(marker6Pattern3Button);
			marker6Pattern3Button.setSelected(false);
			marker6PatternConstraints2.gridx++;
			marker6PatternPanel2.add(marker6Pattern4Button);
			marker6Pattern4Button.setSelected(false);
			marker6PatternConstraints2.gridx++;

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
			marker7PatternPanel1.add(marker7Button);
			marker7PatternConstraints1.gridx++;
			marker7PatternPanel1.add(marker7ColorButton);
			marker7PatternConstraints1.gridx++;
			marker7PatternPanel1.add(marker7RemoveButton);

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

			marker7PatternPanel2.add(marker7Pattern1Button);
			marker7Pattern1Button.setSelected(false);
			marker7PatternConstraints2.gridx++;
			marker7PatternPanel2.add(marker7Pattern2Button);
			marker7Pattern2Button.setSelected(false);
			marker7PatternConstraints2.gridx++;
			marker7PatternPanel2.add(marker7Pattern3Button);
			marker7Pattern3Button.setSelected(false);
			marker7PatternConstraints2.gridx++;
			marker7PatternPanel2.add(marker7Pattern4Button);
			marker7Pattern4Button.setSelected(false);
			marker7PatternConstraints2.gridx++;

			// Marker panel
			markerPanel.setBorder(BorderFactory.createTitledBorder("Labels"));
			markerConstraints.anchor = GridBagConstraints.NORTHWEST;
			markerConstraints.fill = GridBagConstraints.HORIZONTAL;
			markerConstraints.gridwidth = 1;
			markerConstraints.gridheight = 1;
			markerConstraints.gridx = 0;
			markerConstraints.gridy = 0;
			markerPanel.setLayout(markerLayout);
			markerPanel.add(addMarkerButton,markerConstraints);
			markerConstraints.gridy++;
			markerPanel.add(batchMarkerButton,markerConstraints);
			markerConstraints.gridy++;
			
			if(numOfMarkers>0) {
				marker1Button.setSelected(false);
				markerPanel.add(marker1PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker1PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
			}
			if(numOfMarkers>1) {
				marker2Button.setSelected(false);
				markerPanel.add(marker2PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker2PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
			}
			if(numOfMarkers>2) {
				marker3Button.setSelected(false);
				markerPanel.add(marker3PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker3PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
			}
			if(numOfMarkers>3) {
				marker4Button.setSelected(false);
				markerPanel.add(marker4PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker4PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
			}
			if(numOfMarkers>4) {
				marker5Button.setSelected(false);
				markerPanel.add(marker5PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker5PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
			}
			if(numOfMarkers>5) {
				marker6Button.setSelected(false);
				markerPanel.add(marker6PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker6PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
			}
			if(numOfMarkers>6) {
				marker7Button.setSelected(false);
				markerPanel.add(marker7PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker7PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
			}
			
			
			if(currentMode==1) {Toolbar.getInstance().setTool(Toolbar.POINT);}
			
			// Visualization panel 1
			visualizationPanel1.setBorder(BorderFactory.createTitledBorder("Visualization"));
			GridBagLayout visualizationLayout1 = new GridBagLayout();
			GridBagConstraints visualizationConstraints1 = new GridBagConstraints();
			visualizationConstraints1.anchor = GridBagConstraints.NORTHWEST;
			visualizationConstraints1.fill = GridBagConstraints.HORIZONTAL;
			visualizationConstraints1.gridwidth = 1;
			visualizationConstraints1.gridheight = 1;
			visualizationConstraints1.gridx = 0;
			visualizationConstraints1.gridy = 0;
			
			visualizationPanel1.setLayout(visualizationLayout1);
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
			visualizationPanel2.setBorder(BorderFactory.createTitledBorder("Visualization"));
			GridBagLayout visualizationLayout2 = new GridBagLayout();
			GridBagConstraints visualizationConstraints2 = new GridBagConstraints();
			visualizationConstraints2.anchor = GridBagConstraints.NORTHWEST;
			visualizationConstraints2.fill = GridBagConstraints.HORIZONTAL;
			visualizationConstraints2.gridwidth = 1;
			visualizationConstraints2.gridheight = 1;
			visualizationConstraints2.gridx = 0;
			visualizationConstraints2.gridy = 0;
			visualizationPanel2.setLayout(visualizationLayout2);

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
			
			// Annotation panel
			annotationPanel.setBorder(BorderFactory.createTitledBorder("Annotation"));
			GridBagLayout annotationLayout = new GridBagLayout();
			GridBagConstraints annotationConstraints = new GridBagConstraints();
			annotationConstraints.anchor = GridBagConstraints.NORTHWEST;
			annotationConstraints.fill = GridBagConstraints.HORIZONTAL;
			annotationConstraints.gridwidth = 1;
			annotationConstraints.gridheight = 1;
			annotationConstraints.gridx = 0;
			annotationConstraints.gridy = 0;
			//annotationConstraints.insets = new Insets(5, 5, 6, 6);
			annotationPanel.setLayout(annotationLayout);

			annotationPanel.add(newObjectButton, annotationConstraints);
			annotationConstraints.gridy++;
			newObjectButton.setSelected(true);
			if(currentMode==0) {Toolbar.getInstance().setTool(Toolbar.FREEROI);}
			
			annotationPanel.add(removeObjectButton, annotationConstraints);
			annotationConstraints.gridy++;
			removeObjectButton.setSelected(false);
			annotationPanel.add(mergeObjectsButton, annotationConstraints);
			annotationConstraints.gridy++;
			mergeObjectsButton.setSelected(false);
			annotationPanel.add(splitObjectsButton, annotationConstraints);
			annotationConstraints.gridy++;
			splitObjectsButton.setSelected(false);
			annotationPanel.add(swapObjectClassButton, annotationConstraints);
			annotationConstraints.gridy++;
			swapObjectClassButton.setSelected(false);
			
			// Classes panel
			classesPanel.setBorder(BorderFactory.createTitledBorder("Labels"));
			classesConstraints.anchor = GridBagConstraints.NORTHWEST;
			classesConstraints.fill = GridBagConstraints.HORIZONTAL;
			classesConstraints.gridwidth = 1;
			classesConstraints.gridheight = 1;
			classesConstraints.gridx = 0;
			classesConstraints.gridy = 0;
			//classesConstraints.insets = new Insets(5, 5, 6, 6);
			classesPanel.setLayout(classesLayout);
			
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

			// thresholding marker panel
			JLabel l1,l2;
			l1 = new JLabel("Intensity thresholding");
			l2 = new JLabel("Area thresholding");
			JPanel thresholdingMarkerPanel = new JPanel(), intensityThresholdingMarkerPanel = new JPanel(), areaThresholdingMarkerPanel = new JPanel();
			thresholdingMarkerPanel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagLayout thresholdingMarkerPanelLayout = new GridBagLayout();
			GridBagConstraints thresholdingMarkerPanelConstraints = new GridBagConstraints(), intensityThresholdingMarkerPanelConstraints = new GridBagConstraints(), areaThresholdingMarkerPanelConstraints = new GridBagConstraints();
			thresholdingMarkerPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			thresholdingMarkerPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			thresholdingMarkerPanelConstraints.gridwidth = 1;
			thresholdingMarkerPanelConstraints.gridheight = 1;
			thresholdingMarkerPanelConstraints.gridx = 0;
			thresholdingMarkerPanelConstraints.gridy = 0;
			intensityThresholdingMarkerPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			intensityThresholdingMarkerPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			intensityThresholdingMarkerPanelConstraints.gridwidth = 1;
			intensityThresholdingMarkerPanelConstraints.gridheight = 1;
			intensityThresholdingMarkerPanelConstraints.gridx = 0;
			intensityThresholdingMarkerPanelConstraints.gridy = 0;
			areaThresholdingMarkerPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			areaThresholdingMarkerPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			areaThresholdingMarkerPanelConstraints.gridwidth = 1;
			areaThresholdingMarkerPanelConstraints.gridheight = 1;
			areaThresholdingMarkerPanelConstraints.gridx = 0;
			areaThresholdingMarkerPanelConstraints.gridy = 0;
			
			
			thresholdingMarkerPanel.setLayout(thresholdingMarkerPanelLayout);
			thresholdingMarkerPanel.add(l1,thresholdingMarkerPanelConstraints);
			thresholdingMarkerPanelConstraints.gridy++;
			
			intensityThresholdingMarkerPanel.add(intensityThresholdingScrollBar,intensityThresholdingMarkerPanelConstraints);
			intensityThresholdingMarkerPanelConstraints.gridx++;
			intensityThresholdingTextArea.setPreferredSize( new Dimension( 50, 24 ) );
			intensityThresholdingMarkerPanel.add(intensityThresholdingTextArea,intensityThresholdingMarkerPanelConstraints);
			intensityThresholdingMarkerPanelConstraints.gridx++;
			intensityThresholdingMarkerPanel.add(setIntensityThresholdButton,intensityThresholdingMarkerPanelConstraints);
			
			thresholdingMarkerPanel.add(intensityThresholdingMarkerPanel,thresholdingMarkerPanelConstraints);
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
			
			JPanel acceptanceThresholdingMarkerPanel = new JPanel();
			acceptanceThresholdingMarkerPanel.setBorder(BorderFactory.createTitledBorder(""));
			GridBagConstraints acceptanceThresholdingMarkerPanelConstraints = new GridBagConstraints();
			acceptanceThresholdingMarkerPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
			acceptanceThresholdingMarkerPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
			acceptanceThresholdingMarkerPanelConstraints.gridwidth = 1;
			acceptanceThresholdingMarkerPanelConstraints.gridheight = 1;
			acceptanceThresholdingMarkerPanelConstraints.gridx = 0;
			acceptanceThresholdingMarkerPanelConstraints.gridy = 0;
			acceptanceThresholdingMarkerPanel.add(okMarkerButton,acceptanceThresholdingMarkerPanelConstraints);
			acceptanceThresholdingMarkerPanelConstraints.gridx++;
			acceptanceThresholdingMarkerPanel.add(cancelMarkerButton,acceptanceThresholdingMarkerPanelConstraints);
			thresholdingMarkerPanel.add(acceptanceThresholdingMarkerPanel,thresholdingMarkerPanelConstraints);
			
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
			leftPanel1.add(visualizationPanel1, leftConstraints1);
			leftConstraints1.gridy++;
			leftPanel1.add(annotationPanel, leftConstraints1);
			leftConstraints1.gridy++;
			leftPanel1.add(classesPanel, leftConstraints1);
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
			leftPanel2.add(visualizationPanel2, leftConstraints2);
			leftConstraints2.gridy++;
			leftPanel2.add(markerPanel, leftConstraints2);
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
			rightPanel1.add(filePanel1, rightConstraints1);
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
			rightPanel2.add(filePanel2, rightConstraints2);
			rightConstraints2.gridy++;
			rightPanel2.add(analysisPanel2, rightConstraints2);
			rightConstraints2.gridy++;
			rightConstraints2.insets = new Insets(5, 5, 6, 6);

			// Bottom panel
			GridBagLayout bottomLayout = new GridBagLayout();
			GridBagConstraints bottomConstraints = new GridBagConstraints();
			bottomPanel.setLayout(bottomLayout);
			bottomConstraints.anchor = GridBagConstraints.NORTHWEST;
			bottomConstraints.fill = GridBagConstraints.HORIZONTAL;
			bottomConstraints.gridwidth = 1;
			bottomConstraints.gridheight = 1;
			bottomConstraints.gridx = 0;
			bottomConstraints.gridy = 0;
			bottomPanel.add(thresholdingMarkerPanel, bottomConstraints);
			bottomConstraints.gridy++;
			bottomPanel.add(thresholdingMarkerPanel, bottomConstraints);
			bottomConstraints.gridy++;
			bottomConstraints.insets = new Insets(5, 5, 6, 6);

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
				displayImage.setPosition(chosenChannel, displayImage.getSlice(), displayImage.getFrame());
				displayImage.updateAndDraw();
				IJ.setThreshold(displayImage, 0, intensityThresholdingScrollBar.getValue(), "Over/Under");
				roiActivationAndDeactivationBasedOnThresholding();
				displayImage.setOverlay(markersOverlay);
				displayImage.updateAndDraw();

				allConstraints.gridx = 0;
				allConstraints.gridy = 2;
				allConstraints.anchor = GridBagConstraints.NORTHEAST;
				allConstraints.weightx = 0;
				allConstraints.weighty = 0;
				all.add(bottomPanel, allConstraints);

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
					nucleiAnnotationButton.removeActionListener(listener);
					nucleiMarkerButton.removeActionListener(listener);
					loadButton1.removeActionListener(listener);
					loadButton2.removeActionListener(listener);
					saveButton1.removeActionListener(listener);
					saveButton2.removeActionListener(listener);
					//filterNucleiButton.removeActionListener(listener);
					analyzeClassesButton.removeActionListener(listener);
					classSnapshotButton.removeActionListener(listener);
					batchClassesMeasurementsButton.removeActionListener(listener);
					analyzeMarkerButton.removeActionListener(listener);
					markerSnapshotButton.removeActionListener(listener);
					batchMarkerMeasurementsButton.removeActionListener(listener);
					newObjectButton.removeActionListener(listener);
					removeObjectButton.removeActionListener(listener);
					splitObjectsButton.removeActionListener(listener);
					mergeObjectsButton.removeActionListener(listener);
					swapObjectClassButton.removeActionListener(listener);
					addClassButton.removeActionListener(listener);
					class1Button.removeActionListener(listener);
					class1ColorButton.removeActionListener(listener);
					class1RemoveButton.removeActionListener(listener);
					if(numOfClasses>0) {class2Button.removeActionListener(listener);class2ColorButton.removeActionListener(listener);class2RemoveButton.removeActionListener(listener);}
					if(numOfClasses>1) {class3Button.removeActionListener(listener);class3ColorButton.removeActionListener(listener);class3RemoveButton.removeActionListener(listener);}
					if(numOfClasses>2) {class4Button.removeActionListener(listener);class4ColorButton.removeActionListener(listener);class4RemoveButton.removeActionListener(listener);}
					if(numOfClasses>3) {class5Button.removeActionListener(listener);class5ColorButton.removeActionListener(listener);class5RemoveButton.removeActionListener(listener);}
					addMarkerButton.removeActionListener(listener);
					batchMarkerButton.removeActionListener(listener);
					visualizeChannel1Button1.removeActionListener(listener);
					visualizeChannel1onlyButton1.removeActionListener(listener);
					visualizeChannel1Button2.removeActionListener(listener);
					visualizeChannel1onlyButton2.removeActionListener(listener);
					visualizeAllChannelsButton1.removeActionListener(listener);
					visualizeAllChannelsButton2.removeActionListener(listener);
					if(numOfMarkers>0) {removeMarker1ButtonFromListener();}
					if(numOfMarkers>1) {removeMarker2ButtonFromListener();}
					if(numOfMarkers>2) {removeMarker3ButtonFromListener();}
					if(numOfMarkers>3) {removeMarker4ButtonFromListener();}
					if(numOfMarkers>4) {removeMarker5ButtonFromListener();}
					if(numOfMarkers>5) {removeMarker6ButtonFromListener();}
					if(numOfMarkers>6) {removeMarker7ButtonFromListener();}
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
				nucleiAnnotationButton.addActionListener(listener);
				nucleiMarkerButton.addActionListener(listener);
				loadButton1.addActionListener(listener);
				loadButton2.addActionListener(listener);
				saveButton1.addActionListener(listener);
				saveButton2.addActionListener(listener);
				//filterNucleiButton.addActionListener(listener);
				analyzeClassesButton.addActionListener(listener);
				classSnapshotButton.addActionListener(listener);
				batchClassesMeasurementsButton.addActionListener(listener);
				analyzeMarkerButton.addActionListener(listener);
				markerSnapshotButton.addActionListener(listener);
				batchMarkerMeasurementsButton.addActionListener(listener);
				newObjectButton.addActionListener(listener);
				removeObjectButton.addActionListener(listener);
				mergeObjectsButton.addActionListener(listener);
				splitObjectsButton.addActionListener(listener);
				swapObjectClassButton.addActionListener(listener);
				addClassButton.addActionListener(listener);
				class1Button.addActionListener(listener);
				class1ColorButton.addActionListener(listener);
				class1RemoveButton.addActionListener(listener);
				addMarkerButton.addActionListener(listener);
				batchMarkerButton.addActionListener(listener);
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
				classColors[1] = findClassColor();
				numOfClasses = 2;
			}
			else {
				if(numOfClasses==2) {
					classesPanel.add(class3Panel,classesConstraints);
					classesConstraints.gridy++;
					class3Button.addActionListener(listener);
					class3ColorButton.addActionListener(listener);
					class3RemoveButton.addActionListener(listener);
					classColors[2] = findClassColor();
					numOfClasses = 3;
				}
				else {
					if(numOfClasses==3) {
						classesPanel.add(class4Panel,classesConstraints);
						classesConstraints.gridy++;
						class4Button.addActionListener(listener);
						class4ColorButton.addActionListener(listener);
						class4RemoveButton.addActionListener(listener);
						classColors[3] = findClassColor();
						numOfClasses = 4;
					}
					else {
						if(numOfClasses==4) {
							classesPanel.add(class5Panel,classesConstraints);
							classesConstraints.gridy++;
							class5Button.addActionListener(listener);
							class5ColorButton.addActionListener(listener);
							class5RemoveButton.addActionListener(listener);
							classColors[4] = findClassColor();
							numOfClasses = 5;
						}
					}
				}
			}
			
			repaintAll();
		}
		
		
		/**
		 * Add new marker
		 */
		public void addMarker()
		{	
			for(int j=0;j<4;j++) {
				positiveNucleiForEachMarker[numOfMarkers][j] = new ArrayList<Short>();
			}
			if(numOfMarkers==0) {
				markerPanel.add(marker1PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker1PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
				addMarker1ButtonFromListener();
				numOfMarkers = 1;
			}
			else if(numOfMarkers==1) {
				markerPanel.add(marker2PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker2PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
				addMarker2ButtonFromListener();
				numOfMarkers = 2;
			}
			else if(numOfMarkers==2) {
				markerPanel.add(marker3PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker3PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
				addMarker3ButtonFromListener();
				numOfMarkers = 3;
			}
			else if(numOfMarkers==3) {
				markerPanel.add(marker4PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker4PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
				addMarker4ButtonFromListener();
				numOfMarkers = 4;
			}
			else if(numOfMarkers==4) {
				markerPanel.add(marker5PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker5PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
				addMarker5ButtonFromListener();
				numOfMarkers = 5;
			}
			else if(numOfMarkers==5) {
				markerPanel.add(marker6PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker6PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
				addMarker6ButtonFromListener();
				numOfMarkers = 6;
			}
			else if(numOfMarkers==6) {
				markerPanel.add(marker7PatternPanel1, markerConstraints);
				markerConstraints.gridy++;
				markerPanel.add(marker7PatternPanel2, markerConstraints);
				markerConstraints.gridy++;
				addMarker7ButtonFromListener();
				numOfMarkers = 7;
			}
			
			repaintAll();
		}
	}

	/**
	 * Compute intensity threshold for which the objects become positive
	 */
	void computeIntensityThreshodForEachObject(List<Polygon> [] cellCompartmentObjectsInEachClass) {
		int maxObjectsForOneClass=0;
		for(int c=0;c<numOfClasses;c++) {
			if(cellCompartmentObjectsInEachClass[c].size()>maxObjectsForOneClass) {
				maxObjectsForOneClass = cellCompartmentObjectsInEachClass[c].size(); 
			}
		}
		intensityThresholds = new short[numOfClasses][maxObjectsForOneClass];
		for(int c=0;c<numOfClasses;c++) {
			for(int i=0;i<cellCompartmentObjectsInEachClass[c].size();i++) {
				Polygon fp = cellCompartmentObjectsInEachClass[c].get(i);
				if(fp.npoints>0) {
					short[] intensities = new short[fp.npoints];
					ImageProcessor ipt = displayImage.getStack().getProcessor(chosenChannel);
					for(int p=0;p<fp.npoints;p++) {
						intensities[p] = (short)ipt.getf(fp.xpoints[p],fp.ypoints[p]);
					}
					Arrays.sort(intensities);
					int currentThreshold = (int)((float)fp.npoints - (float)areaThresholdingScrollBar.getValue()*(float)fp.npoints/(float)100);
					//int currentThreshold = (int)((float)fp.npoints - (float)areaThresholdingScrollBar.getValue()*(float)fp.npoints/(float)100);
					if(currentThreshold>=fp.npoints) {currentThreshold = fp.npoints-1;}
					if(currentThreshold<0) {currentThreshold = 0;}
					intensityThresholds[c][i] = intensities[currentThreshold];
				}
				else {
					intensityThresholds[c][i] = 0;
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
				List<Point> ptsToRemove = drawNewObjectContour(xPoints,yPoints,currentClass);
				if(ptsToRemove.size()>0) {
					// remove points that have no neighbors
					// if point has coordinates -1,-1 => this nucleus has to be removed
					if(ptsToRemove.get(0).x!=(-1)) {
						int [] pointsToRemoveIndexes = new int[xPoints.length];
						int nbPointsToRemove=0;
						for(int i=0;i<ptsToRemove.size();i++) {
							for(int u = 0; u< xPoints.length; u++) {
								if(((int)xPoints[u]==ptsToRemove.get(i).x)&&((int)yPoints[u]==ptsToRemove.get(i).y)) {
									pointsToRemoveIndexes[u] = 1;
									nbPointsToRemove++;
								}
							}
						}
						int[] xUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
						int[] yUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
						int currentIndex=0;
						for(int u = 0; u< xPoints.length; u++) {
							if(pointsToRemoveIndexes[u]<1) {
								xUpdatedPoints[currentIndex] = xPoints[u];
								yUpdatedPoints[currentIndex] = yPoints[u];
								currentIndex++;
							}
						}
						//xPoints = null;
						//yPoints = null;
						xPoints = xUpdatedPoints;
						yPoints = yUpdatedPoints;
						
						// add nucleus to the list of nuclei
						Point[] RoiPoints = new Point[xUpdatedPoints.length];
						for(int u = 0; u< xPoints.length; u++) {
							roiFlag[xUpdatedPoints[u]][yUpdatedPoints[u]][0] = currentClass;
							roiFlag[xUpdatedPoints[u]][yUpdatedPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
							roiFlag[xUpdatedPoints[u]][yUpdatedPoints[u]][2] = (short)(overlay.size()-1);
							RoiPoints[u] = new Point(xUpdatedPoints[u],yUpdatedPoints[u]);
						}
						// define polygon and roi corresponding to the new region
						//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
						// save new nucleus as roi in the corresponding class
						objectsInEachClass[currentClass].add(RoiPoints);
					}
				}
				else {
					// add nucleus to the list of nuclei
					Point[] RoiPoints = new Point[xPoints.length];
					for(int u = 0; u< xPoints.length; u++) {
						roiFlag[xPoints[u]][yPoints[u]][0] = currentClass;
						roiFlag[xPoints[u]][yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
						roiFlag[xPoints[u]][yPoints[u]][2] = (short)(overlay.size()-1);
						RoiPoints[u] = new Point(xPoints[u],yPoints[u]);
					}
					// define polygon and roi corresponding to the new region
					//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
					// save new nucleus as roi in the corresponding class
					objectsInEachClass[currentClass].add(RoiPoints);
				}
			}
		}
		// refresh displaying
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();
	}
	/** remove all markers from markers overlay */
	void removeMarkersFromOverlay() {
		if(currentMarker>(-1)) {
			for(int p = 0; p < 4; p++) {
				for(int i = 0; i < positiveNucleiForEachMarker[currentMarker][p].size(); i++) {
					Point[] pts = overlay.get(positiveNucleiForEachMarker[currentMarker][p].get(i)).getContainedPoints();
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
	}
	/** activate/deactivate rois for marker identification based on thresholding */
	void roiActivationAndDeactivationBasedOnThresholding() {
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				if(intensityThresholdingScrollBar.getValue()<intensityThresholds[i][j]) {
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
	int[][][] computeNuclearComponent(){
		IJ.run("Conversions...", " ");
		int[][][] nuclearComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()], nuclei = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
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
		return nuclearComponent;
	}
	/** compute nuclear component array */
	int[][][] computeMembranarComponent(int[][][] nuclearComponent){
		IJ.run("Conversions...", " ");
		int[][][] membranarComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<numOfClasses;i++) {
			int globalIndex = 0, cpt=0;
			while(globalIndex<objectsInEachClass[i].size()) {
				int[][] currentNuclei = new int[displayImage.getWidth()][displayImage.getHeight()];
				for(int j=0;j<25;j++) {
					if(globalIndex<objectsInEachClass[i].size()) {
						//Polygon fp = objectsInEachClass[i].get(globalIndex).getPolygon();
						Point[] fp = objectsInEachClass[i].get(globalIndex);
						for(int k=0;k<fp.length;k++) {
							currentNuclei[fp[k].x][fp[k].y] = j+1;
						}
						globalIndex++;
					}
				}
				ImageProcessor nucleiIP = new FloatProcessor(currentNuclei);
				ImagePlus dilatedNucleiImage1 = new ImagePlus("Diated nuclei, radius = 1", nucleiIP);
				IJ.run(dilatedNucleiImage1, "8-bit", "");
				IJ.run(dilatedNucleiImage1, "Gray Morphology", "radius=1 type=circle operator=dilate");
				ImageProcessor dilatedNucleiIp = dilatedNucleiImage1.getStack().getProcessor(1);
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						boolean nuclearSite=false;
						for(int c=0;c<numOfClasses;c++) {
							if(nuclearComponent[c][x][y]>0) {
								nuclearSite = true;
							}
						}
						if(!nuclearSite) {
							int value = (int)dilatedNucleiIp.getf(x,y);
							if(value>0) {
								boolean membranarSite=false;
								int classRef=0;
								for(int c=0;c<numOfClasses;c++) {
									if(membranarComponent[c][x][y]>0) {
										membranarSite = true;
										classRef = c;
									}
								}
								if(!membranarSite) {
									membranarComponent[i][x][y] = value + cpt*25;
								}
								else {
									//Polygon fp1 = objectsInEachClass[i].get(membranarComponent[classRef][x][y]-1).getPolygon(),
										//	fp2 = objectsInEachClass[i].get(value + cpt*25 -1).getPolygon();
									Point[] fp1 = objectsInEachClass[i].get(membranarComponent[classRef][x][y]-1),
											fp2 = objectsInEachClass[i].get(value + cpt*25 -1);
									double minDistance1=100000, minDistance2=100000;
									for(int k=0;k<fp1.length;k++) {
										if((Math.pow(x-fp1[k].x,2)+Math.pow(y-fp1[k].y,2))<minDistance1){
											minDistance1 = Math.pow(x-fp1[k].x,2)+Math.pow(y-fp1[k].y,2);
										}
									}
									for(int k=0;k<fp2.length;k++) {
										if((Math.pow(x-fp2[k].x,2)+Math.pow(y-fp2[k].y,2))<minDistance2){
											minDistance2 = Math.pow(x-fp2[k].x,2)+Math.pow(y-fp2[k].y,2);
										}
									}
									if(minDistance2<minDistance1) {
										membranarComponent[classRef][x][y] = 0;
										membranarComponent[i][x][y] = value + cpt*25;
									}
								}
							}
						}
					}
				}
				cpt++;
			}
		}
		IJ.run("Conversions...", "scale");
		return membranarComponent;
	}
	/** compute nuclear component array */
	int[][][] computeCytoplasmicComponent(int[][][] nuclearComponent, int[][][] membranarComponent){
		IJ.run("Conversions...", " ");
		int[][][] cytoplasmicComponent = new int[numOfClasses][displayImage.getWidth()][displayImage.getHeight()];
		for(int i=0;i<numOfClasses;i++) {
			int globalIndex = 0, cpt=0;
			while(globalIndex<objectsInEachClass[i].size()) {
				int[][] currentNuclei = new int[displayImage.getWidth()][displayImage.getHeight()];
				for(int j=0;j<25;j++) {
					if(globalIndex<objectsInEachClass[i].size()) {
						//Polygon fp = objectsInEachClass[i].get(globalIndex).getPolygon();
						Point[] fp = objectsInEachClass[i].get(globalIndex);
						for(int k=0;k<fp.length;k++) {
							currentNuclei[fp[k].x][fp[k].y] = j+1;
						}
						globalIndex++;
					}
				}
				ImageProcessor nucleiIP = new FloatProcessor(currentNuclei);
				ImagePlus dilatedNucleiImage = new ImagePlus("Dilated nuclei, radius = 5", nucleiIP);
				IJ.run(dilatedNucleiImage, "8-bit", "");
				IJ.run(dilatedNucleiImage, "Gray Morphology", "radius=5 type=circle operator=dilate");
				ImageProcessor dilatedNucleiIp = dilatedNucleiImage.getStack().getProcessor(1);
				for(int y=0;y<displayImage.getHeight();y++) {
					for(int x=0;x<displayImage.getWidth();x++) {
						boolean nuclearSite=false;
						for(int c=0;c<numOfClasses;c++) {
							if(nuclearComponent[c][x][y]>0) {
								nuclearSite = true;
							}
						}
						if(!nuclearSite) {
							boolean membranarSite=false;
							for(int c=0;c<numOfClasses;c++) {
								if(membranarComponent[c][x][y]>0) {
									membranarSite = true;
								}
							}
							if(!membranarSite) {
								int value = (int)dilatedNucleiIp.getf(x,y);
								if(value>0) {
									boolean cytoplasmicSite=false;
									int classRef=0;
									for(int c=0;c<numOfClasses;c++) {
										if(cytoplasmicComponent[c][x][y]>0) {
											cytoplasmicSite = true;
											classRef = c;
										}
									}
									if(!cytoplasmicSite) {
										
										cytoplasmicComponent[i][x][y] = value + cpt*25;
									}
									else {
										//Polygon fp1 = objectsInEachClass[i].get(cytoplasmicComponent[classRef][x][y]-1).getPolygon(),
											//	fp2 = objectsInEachClass[i].get(value  + cpt*25 -1).getPolygon();
										Point[] fp1 = objectsInEachClass[i].get(cytoplasmicComponent[classRef][x][y]-1),
												fp2 = objectsInEachClass[i].get(value  + cpt*25 -1);
										double minDistance1=100000, minDistance2=100000;
										for(int k=0;k<fp1.length;k++) {
											if((Math.pow(x-fp1[k].x,2)+Math.pow(y-fp1[k].y,2))<minDistance1){
												minDistance1 = Math.pow(x-fp1[k].x,2)+Math.pow(y-fp1[k].y,2);
											}
										}
										for(int k=0;k<fp2.length;k++) {
											if((Math.pow(x-fp2[k].x,2)+Math.pow(y-fp2[k].y,2))<minDistance2){
												minDistance2 = Math.pow(x-fp2[k].x,2)+Math.pow(y-fp2[k].y,2);
											}
										}
										if(minDistance2<minDistance1) {
											cytoplasmicComponent[classRef][x][y] = 0;
											cytoplasmicComponent[i][x][y] = value + cpt*25;
										}
									}
								}
							}
						}
					}
				}
				cpt++;
			}
		}
		IJ.run("Conversions...", "scale");
		return cytoplasmicComponent;
	}
	/** process to define thresholded markers */ 
	private boolean addMarkerWindow()
	{
		/** buttons for marker characterization */
		JRadioButton nuclearRadioButton = new JRadioButton("Nuclear marker");
		nuclearRadioButton.setSelected(true);
		JRadioButton membranarRadioButton = new JRadioButton("Membranar marker");
		membranarRadioButton.setSelected(false);
		JRadioButton cytoplasmicRadioButton = new JRadioButton("Cytoplasmic marker");
		cytoplasmicRadioButton.setSelected(false);
		
		ButtonGroup bg1=new ButtonGroup();    
		bg1.add(nuclearRadioButton);bg1.add(membranarRadioButton);bg1.add(cytoplasmicRadioButton);
		
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
			markerCellcompartment[numOfMarkers-1] = 0;
		}
		else if(membranarRadioButton.isSelected()) {
			markerCellcompartment[numOfMarkers-1] = 1;
		}
		else if(cytoplasmicRadioButton.isSelected()) {
			markerCellcompartment[numOfMarkers-1] = 2;
		}
		
		/** buttons for thresholding decision */
		JRadioButton yesRadioButton = new JRadioButton("Yes");
		yesRadioButton.setSelected(true);
		JRadioButton noRadioButton = new JRadioButton("No");
		noRadioButton.setSelected(false);
		
		JPanel thresholdPanel = new JPanel();
		thresholdPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout thresholdPanelLayout = new GridBagLayout();
		GridBagConstraints thresholdPanelConstraints = new GridBagConstraints();
		thresholdPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		thresholdPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		thresholdPanelConstraints.gridwidth = 1;
		thresholdPanelConstraints.gridheight = 1;
		thresholdPanelConstraints.gridx = 0;
		thresholdPanelConstraints.gridy = 0;
		thresholdPanel.setLayout(thresholdPanelLayout);
		thresholdPanel.add(yesRadioButton,thresholdPanelConstraints);
		thresholdPanelConstraints.gridx++;
		thresholdPanel.add(noRadioButton,thresholdPanelConstraints);
		
		ButtonGroup bg2=new ButtonGroup();    
		bg2.add(yesRadioButton);bg2.add(noRadioButton);
		
		GenericDialogPlus gd2 = new GenericDialogPlus("Marker creation");
		gd2.addMessage("Do you want to identify this marker with a thresholding?");
		gd2.addComponent(thresholdPanel);
		gd2.showDialog();

		if (gd2.wasCanceled())
			return false;

		if(yesRadioButton.isSelected()) {
			/** buttons for thresholding decision */
			JRadioButton channel1RadioButton = new JRadioButton("Channel 1");
			channel1RadioButton.setSelected(true);
			JRadioButton channel2RadioButton = new JRadioButton("Channel 2");
			channel2RadioButton.setSelected(false);
			JRadioButton channel3RadioButton = new JRadioButton("Channel 3");
			channel3RadioButton.setSelected(false);
			JRadioButton channel4RadioButton = new JRadioButton("Channel 4");
			channel4RadioButton.setSelected(false);
			JRadioButton channel5RadioButton = new JRadioButton("Channel 5");
			channel5RadioButton.setSelected(false);
			JRadioButton channel6RadioButton = new JRadioButton("Channel 6");
			channel6RadioButton.setSelected(false);
			JRadioButton channel7RadioButton = new JRadioButton("Channel 7");
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
			gd3.addMessage("Which channel is associated with this channel?");
			gd3.addComponent(currentchannelPanel);
			gd3.showDialog();

			if (gd3.wasCanceled())
				return false;

			chosenChannel = 1;
			if(channel2RadioButton.isSelected()) {chosenChannel= 2;}
			else if(channel3RadioButton.isSelected()) {chosenChannel = 3;}
			else if(channel4RadioButton.isSelected()) {chosenChannel = 4;}
			else if(channel5RadioButton.isSelected()) {chosenChannel = 5;}
			else if(channel6RadioButton.isSelected()) {chosenChannel = 6;}
			else if(channel7RadioButton.isSelected()) {chosenChannel = 7;}
			channelForMarker[numOfMarkers-1] = chosenChannel;
			
			currentMode = 2;
			currentMarker = numOfMarkers-1;
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
			
			int[][][] nuclearComponent = computeNuclearComponent();
			if(nuclearRadioButton.isSelected()) {
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
				int[][][] membranarComponent = computeMembranarComponent(nuclearComponent);
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
				int[][][] membranarForCytoplasmicComponent = computeMembranarComponent(nuclearComponent), cytoplasmicComponent = computeCytoplasmicComponent(nuclearComponent, membranarForCytoplasmicComponent);
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
			ImageProcessor ipt = displayImage.getStack().getProcessor(chosenChannel);
			int maxIntensity=0;
			for(int y=0; y<displayImage.getHeight(); y++)
			{
				for(int x=0; x<displayImage.getWidth(); x++)
				{
					int value = (int)ipt.getf(x,y);
					if(value>maxIntensity) {maxIntensity = value;}
				}
			}
			intensityThresholdingScrollBar.setMaximum(maxIntensity);
			intensityThresholdingScrollBar.setValue(maxIntensity/2);
			intensityThresholdingTextArea.setText("" + maxIntensity/2);
			intensityThresholdingTextArea.setEditable(false);
			thresholdForMarker[numOfMarkers-1][1] = maxIntensity/2;
			computeIntensityThreshodForEachObject(cellComponentInEachClass);
			areaThresholdingScrollBar.setValue(35);
			areaThresholdingTextArea.setText("" + 35);
			areaThresholdingTextArea.setEditable(false);
			thresholdForMarker[numOfMarkers-1][0] = 35;
			
			intensityThresholdingScrollBar.addChangeListener(new ChangeListener() {

				@Override
				public void stateChanged(ChangeEvent ce) {
					IJ.setThreshold(displayImage, 0, ((JSlider) ce.getSource()).getValue(), "Over/Under");
					roiActivationAndDeactivationBasedOnThresholding();
					intensityThresholdingTextArea.setText("" + ((JSlider) ce.getSource()).getValue());
					thresholdForMarker[numOfMarkers-1][1] = intensityThresholdingScrollBar.getValue();
				}
			});

			areaThresholdingScrollBar.addChangeListener(new ChangeListener() {

				@Override
				public void stateChanged(ChangeEvent arg0) {
					computeIntensityThreshodForEachObject(cellComponentInEachClass);
					roiActivationAndDeactivationBasedOnThresholding();
					areaThresholdingTextArea.setText("" + ((JSlider) arg0.getSource()).getValue());
					thresholdForMarker[numOfMarkers-1][0] = areaThresholdingScrollBar.getValue(); 
					displayImage.updateAndDraw();
				}
			});


			okMarkerButton.addActionListener(listener);
			cancelMarkerButton.addActionListener(listener);
			setIntensityThresholdButton.addActionListener(listener);
			setAreaThresholdButton.addActionListener(listener);
			
			SwingUtilities.invokeLater(
					new Runnable() {
						public void run() {
							win = new CustomWindow(displayImage);
							win.pack();
						}
					});
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
	/** batch process markers */ 
	private void batchMarker()
	{
		boolean batchToDo=false;
		for(int i=0;i<MAX_NUM_MARKERS;i++) {
			if(channelForMarker[i]>(-1)) {batchToDo = true;}
		}
		if(!batchToDo) {
			IJ.showMessage("You first need to define marker components by thresholding channels in order to batch process a set of images.");
		}
		else {
			boolean measurementsBatchProcess = false;
			switch ( JOptionPane.showConfirmDialog( null, "Do you also want to batch process measurements?", "Measurements", JOptionPane.YES_NO_OPTION ) )
			{
			case JOptionPane.YES_OPTION:
				measurementsBatchProcess = true;
				break;
			case JOptionPane.NO_OPTION:
				measurementsBatchProcess = false;
				break;
			}
			
			imageFolder = "Null";
			segmentationFolder = "Null";
			markerFolder = "Null";
			measurementsFolder = "Null";

			/** JButton for batch processing */
			JButton imageFolderButton = new JButton("Image folder");
			JButton segmentationFolderButton = new JButton("Segmentation folder");
			JButton markerFolderButton = new JButton("Marker folder");
			JButton measurementsFolderButton = new JButton("Measurements folder");
			
			JTextArea imageFolderQuestion = new JTextArea("Where is the folder with the input images?");
			imageFolderQuestion.setEditable(false);
			JTextArea segmentationFolderQuestion = new JTextArea("Where is the folder with the segmented input images?");
			segmentationFolderQuestion.setEditable(false);
			JTextArea markerFolderQuestion = new JTextArea("Where is the destination folder for the marker images?");
			markerFolderQuestion.setEditable(false);
			JTextArea measurmentsFolderQuestion = new JTextArea("Where is the destination folder for the measurements?");
			measurmentsFolderQuestion.setEditable(false);
						
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
			batchPanel.add(markerFolderQuestion,batchPanelConstraints);
			batchPanelConstraints.gridx++;
			batchPanel.add(markerFolderButton,batchPanelConstraints);
			batchPanelConstraints.gridy++;
			batchPanelConstraints.gridx=0;
			if(measurementsBatchProcess) {
				batchPanel.add(measurmentsFolderQuestion,batchPanelConstraints);
				batchPanelConstraints.gridx++;
				batchPanel.add(measurementsFolderButton,batchPanelConstraints);
				batchPanelConstraints.gridy++;
			}

			GenericDialogPlus gd = new GenericDialogPlus("Batch processing for marker identification");
			gd.addComponent(batchPanel);

			imageFolderButton.addActionListener(new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent arg0) {
					DirectoryChooser imageChooser = new DirectoryChooser("Input images folder");
					imageFolder = imageChooser.getDirectory();
				}
			});

			segmentationFolderButton.addActionListener(new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent arg0) {
					DirectoryChooser segmentationChooser = new DirectoryChooser("Segmentation images folder");
					segmentationFolder = segmentationChooser.getDirectory();
				}
			});
			markerFolderButton.addActionListener(new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent arg0) {
					DirectoryChooser markerChooser = new DirectoryChooser("Marker images folder");
					markerFolder = markerChooser.getDirectory();
				}
			});
			measurementsFolderButton.addActionListener(new ActionListener() {

				@Override
				public void actionPerformed(ActionEvent arg0) {
					DirectoryChooser measurementsChooser = new DirectoryChooser("Measurements folder");
					measurementsFolder = measurementsChooser.getDirectory();
				}
			});

			gd.showDialog();

			if (gd.wasCanceled()) {
				for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
				for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
				for( ActionListener al : markerFolderButton.getActionListeners() ) {markerFolderButton.removeActionListener( al );}
				for( ActionListener al : measurementsFolderButton.getActionListeners() ) {measurementsFolderButton.removeActionListener( al );}
				return;
			}

			if (gd.wasOKed()) {
				for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
				for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
				for( ActionListener al : markerFolderButton.getActionListeners() ) {markerFolderButton.removeActionListener( al );}
				for( ActionListener al : measurementsFolderButton.getActionListeners() ) {measurementsFolderButton.removeActionListener( al );}
				if(imageFolder=="Null") {
					IJ.showMessage("You need to define a folder with the input images to process.");
					return;
				}
				if(segmentationFolder=="Null") {
					IJ.showMessage("You need to define a folder with the segmented input images to process.");
					return;
				}
				if(markerFolder=="Null") {
					IJ.showMessage("You need to define a folder with the marker images associated with the input images to process.");
					return;
				}
				if(measurementsBatchProcess) {
					if(measurementsFolder=="Null") {
						IJ.showMessage("You need to define a destination folder for the measurements.");
						return;
					}
				}
				File imageFile = new File(imageFolder), segmentationFile = new File(segmentationFolder), markerFile = new File(markerFolder), measurementsFile = new File(measurementsFolder);
				for (File imageFileEntry : imageFile.listFiles()) {
					if (!imageFileEntry.isDirectory()) {
			        	String[] currentImageFile = imageFileEntry.getName().split("\\.");
			        	boolean ok=false;
			        	for (File segmentationFileEntry : segmentationFile.listFiles()) {
			        		String[] currentSegmentationFile = segmentationFileEntry.getName().split("\\.");
			        		if(currentSegmentationFile[0].equals(currentImageFile[0])) {ok=true;}
			        	}
			        	if(!ok) {
			        		IJ.showMessage("For each input image in the input image folder, there must be a segmentation image with the same name in the segmentation folder.");
			        		return;
			        	}
						if(measurementsBatchProcess) {
							ok = false;
							for (File markerFileEntry : markerFile.listFiles()) {
								String[] markerSegmentationFile = markerFileEntry.getName().split("\\.");
								if(markerSegmentationFile[0].equals(currentImageFile[0])) {ok=true;}
							}
							if(!ok) {
								IJ.showMessage("For each input image in the input image folder, there must be a marker image with the same name in the marker folder.");
								return;
							}
						}
			        }
				}

				
				JTextArea marker1Sentence = new JTextArea("Marker 1 does not coincide with:");
				marker1Sentence.setEditable(false);
				JRadioButton marker1RadioButton_1 = new JRadioButton("Marker 1");
				marker1RadioButton_1.setEnabled(false);
				JRadioButton marker2RadioButton_1 = new JRadioButton("Marker 2");
				marker2RadioButton_1.setSelected(false);
				JRadioButton marker3RadioButton_1 = new JRadioButton("Marker 3");
				marker3RadioButton_1.setSelected(false);
				JRadioButton marker4RadioButton_1 = new JRadioButton("Marker 4");
				marker4RadioButton_1.setSelected(false);
				JRadioButton marker5RadioButton_1 = new JRadioButton("Marker 5");
				marker5RadioButton_1.setSelected(false);
				JRadioButton marker6RadioButton_1 = new JRadioButton("Marker 6");
				marker6RadioButton_1.setSelected(false);
				JRadioButton marker7RadioButton_1 = new JRadioButton("Marker 7");
				marker7RadioButton_1.setSelected(false);

				JTextArea marker2Sentence = new JTextArea("Marker 2 does not coincide with:");
				marker2Sentence.setEditable(false);
				JRadioButton marker1RadioButton_2 = new JRadioButton("Marker 1");
				marker1RadioButton_2.setSelected(false);
				JRadioButton marker2RadioButton_2 = new JRadioButton("Marker 2");
				marker2RadioButton_2.setEnabled(false);
				JRadioButton marker3RadioButton_2 = new JRadioButton("Marker 3");
				marker3RadioButton_2.setSelected(false);
				JRadioButton marker4RadioButton_2 = new JRadioButton("Marker 4");
				marker4RadioButton_2.setSelected(false);
				JRadioButton marker5RadioButton_2 = new JRadioButton("Marker 5");
				marker5RadioButton_2.setSelected(false);
				JRadioButton marker6RadioButton_2 = new JRadioButton("Marker 6");
				marker6RadioButton_2.setSelected(false);
				JRadioButton marker7RadioButton_2 = new JRadioButton("Marker 7");
				marker7RadioButton_2.setSelected(false);

				JTextArea marker3Sentence = new JTextArea("Marker 3 does not coincide with:");
				marker3Sentence.setEditable(false);
				JRadioButton marker1RadioButton_3 = new JRadioButton("Marker 1");
				marker1RadioButton_3.setSelected(false);
				JRadioButton marker2RadioButton_3 = new JRadioButton("Marker 2");
				marker2RadioButton_3.setSelected(false);
				JRadioButton marker3RadioButton_3 = new JRadioButton("Marker 3");
				marker3RadioButton_3.setEnabled(false);
				JRadioButton marker4RadioButton_3 = new JRadioButton("Marker 4");
				marker4RadioButton_3.setSelected(false);
				JRadioButton marker5RadioButton_3 = new JRadioButton("Marker 5");
				marker5RadioButton_3.setSelected(false);
				JRadioButton marker6RadioButton_3 = new JRadioButton("Marker 6");
				marker6RadioButton_3.setSelected(false);
				JRadioButton marker7RadioButton_3 = new JRadioButton("Marker 7");
				marker7RadioButton_3.setSelected(false);

				JTextArea marker4Sentence = new JTextArea("Marker 4 does not coincide with:");
				marker4Sentence.setEditable(false);
				JRadioButton marker1RadioButton_4 = new JRadioButton("Marker 1");
				marker1RadioButton_4.setSelected(false);
				JRadioButton marker2RadioButton_4 = new JRadioButton("Marker 2");
				marker2RadioButton_4.setSelected(false);
				JRadioButton marker3RadioButton_4 = new JRadioButton("Marker 3");
				marker3RadioButton_4.setSelected(false);
				JRadioButton marker4RadioButton_4 = new JRadioButton("Marker 4");
				marker4RadioButton_4.setEnabled(false);
				JRadioButton marker5RadioButton_4 = new JRadioButton("Marker 5");
				marker5RadioButton_4.setSelected(false);
				JRadioButton marker6RadioButton_4 = new JRadioButton("Marker 6");
				marker6RadioButton_4.setSelected(false);
				JRadioButton marker7RadioButton_4 = new JRadioButton("Marker 7");
				marker7RadioButton_4.setSelected(false);

				JTextArea marker5Sentence = new JTextArea("Marker 5 does not coincide with:");
				marker5Sentence.setEditable(false);
				JRadioButton marker1RadioButton_5 = new JRadioButton("Marker 1");
				marker1RadioButton_5.setSelected(false);
				JRadioButton marker2RadioButton_5 = new JRadioButton("Marker 2");
				marker2RadioButton_5.setSelected(false);
				JRadioButton marker3RadioButton_5 = new JRadioButton("Marker 3");
				marker3RadioButton_5.setSelected(false);
				JRadioButton marker4RadioButton_5 = new JRadioButton("Marker 4");
				marker4RadioButton_5.setSelected(false);
				JRadioButton marker5RadioButton_5 = new JRadioButton("Marker 5");
				marker5RadioButton_5.setEnabled(false);
				JRadioButton marker6RadioButton_5 = new JRadioButton("Marker 6");
				marker6RadioButton_5.setSelected(false);
				JRadioButton marker7RadioButton_5 = new JRadioButton("Marker 7");
				marker7RadioButton_5.setSelected(false);

				JTextArea marker6Sentence = new JTextArea("Marker 6 does not coincide with:");
				marker6Sentence.setEditable(false);
				JRadioButton marker1RadioButton_6 = new JRadioButton("Marker 1");
				marker1RadioButton_6.setSelected(false);
				JRadioButton marker2RadioButton_6 = new JRadioButton("Marker 2");
				marker2RadioButton_6.setSelected(false);
				JRadioButton marker3RadioButton_6 = new JRadioButton("Marker 3");
				marker3RadioButton_6.setSelected(false);
				JRadioButton marker4RadioButton_6 = new JRadioButton("Marker 4");
				marker4RadioButton_6.setSelected(false);
				JRadioButton marker5RadioButton_6 = new JRadioButton("Marker 5");
				marker5RadioButton_6.setSelected(false);
				JRadioButton marker6RadioButton_6 = new JRadioButton("Marker 6");
				marker6RadioButton_6.setEnabled(false);
				JRadioButton marker7RadioButton_6 = new JRadioButton("Marker 7");
				marker7RadioButton_6.setSelected(false);

				JTextArea marker7Sentence = new JTextArea("Marker 7 does not coincide with:");
				marker7Sentence.setEditable(false);
				JRadioButton marker1RadioButton_7 = new JRadioButton("Marker 1");
				marker1RadioButton_7.setSelected(false);
				JRadioButton marker2RadioButton_7 = new JRadioButton("Marker 2");
				marker2RadioButton_7.setSelected(false);
				JRadioButton marker3RadioButton_7 = new JRadioButton("Marker 3");
				marker3RadioButton_7.setSelected(false);
				JRadioButton marker4RadioButton_7 = new JRadioButton("Marker 4");
				marker4RadioButton_7.setSelected(false);
				JRadioButton marker5RadioButton_7 = new JRadioButton("Marker 5");
				marker5RadioButton_7.setSelected(false);
				JRadioButton marker6RadioButton_7 = new JRadioButton("Marker 6");
				marker6RadioButton_7.setSelected(false);
				JRadioButton marker7RadioButton_7 = new JRadioButton("Marker 7");
				marker7RadioButton_7.setEnabled(false);

				if(numOfMarkers>1) {
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
					if(numOfMarkers>2) {
						nonOverlappingMarkersPanel1_2.add(marker3RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfMarkers>3) {
						nonOverlappingMarkersPanel1_2.add(marker4RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfMarkers>4) {
						nonOverlappingMarkersPanel1_2.add(marker5RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfMarkers>5) {
						nonOverlappingMarkersPanel1_2.add(marker6RadioButton_1,nonOverlappingMarkersPanelConstraints1_2);
						nonOverlappingMarkersPanelConstraints1_2.gridx++;
					}
					if(numOfMarkers>6) {
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
					if(numOfMarkers>2) {
						nonOverlappingMarkersPanel2_2.add(marker3RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfMarkers>3) {
						nonOverlappingMarkersPanel2_2.add(marker4RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfMarkers>4) {
						nonOverlappingMarkersPanel2_2.add(marker5RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfMarkers>5) {
						nonOverlappingMarkersPanel2_2.add(marker6RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					if(numOfMarkers>6) {
						nonOverlappingMarkersPanel2_2.add(marker7RadioButton_2,nonOverlappingMarkersPanelConstraints2_1);
						nonOverlappingMarkersPanelConstraints2_1.gridx++;
					}
					nonOverlappingMarkersPanelConstraints2_1.gridy++;
					nonOverlappingMarkersPanelConstraints2_1.gridx=0;
					
					if(numOfMarkers>2) {
						nonOverlappingMarkersPanel3_1.add(marker3Sentence,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridy++;
						
						nonOverlappingMarkersPanel3_2.add(marker1RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridx++;
						nonOverlappingMarkersPanel3_2.add(marker2RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridx++;
						nonOverlappingMarkersPanel3_2.add(marker3RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
						nonOverlappingMarkersPanelConstraints3_1.gridx++;
						if(numOfMarkers>3) {
							nonOverlappingMarkersPanel3_2.add(marker4RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						if(numOfMarkers>4) {
							nonOverlappingMarkersPanel3_2.add(marker5RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						if(numOfMarkers>5) {
							nonOverlappingMarkersPanel3_2.add(marker6RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						if(numOfMarkers>6) {
							nonOverlappingMarkersPanel3_2.add(marker7RadioButton_3,nonOverlappingMarkersPanelConstraints3_1);
							nonOverlappingMarkersPanelConstraints3_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints3_1.gridy++;
						nonOverlappingMarkersPanelConstraints3_1.gridx=0;
					}
					
					if(numOfMarkers>3) {
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
						if(numOfMarkers>4) {
							nonOverlappingMarkersPanel4_2.add(marker5RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
							nonOverlappingMarkersPanelConstraints4_1.gridx++;
						}
						if(numOfMarkers>5) {
							nonOverlappingMarkersPanel4_2.add(marker6RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
							nonOverlappingMarkersPanelConstraints4_1.gridx++;
						}
						if(numOfMarkers>6) {
							nonOverlappingMarkersPanel4_2.add(marker7RadioButton_4,nonOverlappingMarkersPanelConstraints4_1);
							nonOverlappingMarkersPanelConstraints4_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints4_1.gridy++;
						nonOverlappingMarkersPanelConstraints4_1.gridx=0;
					}
					
					if(numOfMarkers>4) {
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
						if(numOfMarkers>5) {
							nonOverlappingMarkersPanel5_2.add(marker6RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
							nonOverlappingMarkersPanelConstraints5_1.gridx++;
						}
						if(numOfMarkers>6) {
							nonOverlappingMarkersPanel5_2.add(marker7RadioButton_5,nonOverlappingMarkersPanelConstraints5_1);
							nonOverlappingMarkersPanelConstraints5_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints5_1.gridy++;
						nonOverlappingMarkersPanelConstraints5_1.gridx=0;
					}
					
					if(numOfMarkers>5) {
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
						if(numOfMarkers>6) {
							nonOverlappingMarkersPanel6_2.add(marker7RadioButton_6,nonOverlappingMarkersPanelConstraints6_1);
							nonOverlappingMarkersPanelConstraints6_1.gridx++;
						}
						nonOverlappingMarkersPanelConstraints6_1.gridy++;
						nonOverlappingMarkersPanelConstraints6_1.gridx=0;
					}
					
					if(numOfMarkers>6) {
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
					switch (numOfMarkers) {
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
					
					gd2.showDialog();
					
					if(gd2.wasCanceled()) {
						return;
					}
				}

				
				byte[] markerCellcompartmentMem = new byte[]{0,0,0,0,0,0,0}; 
				byte[] channelForMarkerMem = new byte[]{-1,-1,-1,-1,-1,-1,-1};
				int[][] thresholdForMarkerMem = new int[][]{{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1}};
				for(int p=0;p<MAX_NUM_MARKERS;p++) {
					markerCellcompartmentMem[p] = markerCellcompartment[p];
					channelForMarkerMem[p] = channelForMarker[p];
					thresholdForMarkerMem[p][0] = thresholdForMarker[p][0];
					thresholdForMarkerMem[p][1] = thresholdForMarker[p][1];
				}
				
				for (File imageFileEntry : imageFile.listFiles()) {
					if (!imageFileEntry.isDirectory()) {
						String[] currentImageFile = imageFileEntry.getName().split("\\.");
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
						
						//Build GUI
						/*SwingUtilities.invokeLater(
								new Runnable() {
									public void run() {
										win = new CustomWindow(displayImage);
										win.pack();
									}
								});*/
						
						initializeMarkerButtons();
						int actualNumOfMarkers = numOfMarkers;
						ImagePlus segmentedImage = opener.openImage(segmentationFolder+currentSegmentationFile);
						loadNucleiSegmentations(segmentedImage);
						
						currentMarker=0;
						for(int p=0;p<actualNumOfMarkers;p++) {
							addNewMarker();
							updateAnnotateMarker(numOfMarkers-1);
							if(channelForMarkerMem[p]>(-1)) {
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
								int[][][] nuclearComponent = computeNuclearComponent();
								if(markerCellcompartmentMem[p]==0) {
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
								else if(markerCellcompartmentMem[p]==1) {
									int[][][] membranarComponent = computeMembranarComponent(nuclearComponent);
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
								else if(markerCellcompartmentMem[p]==2) {
									int[][][] membranarForCytoplasmicComponent = computeMembranarComponent(nuclearComponent), cytoplasmicComponent = computeCytoplasmicComponent(nuclearComponent, membranarForCytoplasmicComponent);
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
								chosenChannel = channelForMarkerMem[p];
								areaThresholdingScrollBar.setValue(thresholdForMarkerMem[p][0]);
								intensityThresholdingScrollBar.setValue(thresholdForMarkerMem[p][1]);
								computeIntensityThreshodForEachObject(cellComponentInEachClass);
								roiActivationAndDeactivationBasedOnThresholding();
							}
							updateModeRadioButtons(1);
						}
						
						// incompatibilities between markers
						if(numOfMarkers>1) {
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
						if(numOfMarkers>2) {
							if(marker1RadioButton_3.isSelected()) {removeIncompatibility(2,0);}
							if(marker2RadioButton_3.isSelected()) {removeIncompatibility(2,1);}
							if(marker4RadioButton_3.isSelected()) {removeIncompatibility(2,3);}
							if(marker5RadioButton_3.isSelected()) {removeIncompatibility(2,4);}
							if(marker6RadioButton_3.isSelected()) {removeIncompatibility(2,5);}
							if(marker7RadioButton_3.isSelected()) {removeIncompatibility(2,6);}
						}
						if(numOfMarkers>3) {
							if(marker1RadioButton_4.isSelected()) {removeIncompatibility(3,0);}
							if(marker2RadioButton_4.isSelected()) {removeIncompatibility(3,1);}
							if(marker3RadioButton_4.isSelected()) {removeIncompatibility(3,2);}
							if(marker5RadioButton_4.isSelected()) {removeIncompatibility(3,4);}
							if(marker6RadioButton_4.isSelected()) {removeIncompatibility(3,5);}
							if(marker7RadioButton_4.isSelected()) {removeIncompatibility(3,6);}
						}
						if(numOfMarkers>4) {
							if(marker1RadioButton_5.isSelected()) {removeIncompatibility(4,0);}
							if(marker2RadioButton_5.isSelected()) {removeIncompatibility(4,1);}
							if(marker3RadioButton_5.isSelected()) {removeIncompatibility(4,2);}
							if(marker4RadioButton_5.isSelected()) {removeIncompatibility(4,3);}
							if(marker6RadioButton_5.isSelected()) {removeIncompatibility(4,5);}
							if(marker7RadioButton_5.isSelected()) {removeIncompatibility(4,6);}
						}
						if(numOfMarkers>5) {
							if(marker1RadioButton_6.isSelected()) {removeIncompatibility(5,0);}
							if(marker2RadioButton_6.isSelected()) {removeIncompatibility(5,1);}
							if(marker3RadioButton_6.isSelected()) {removeIncompatibility(5,2);}
							if(marker4RadioButton_6.isSelected()) {removeIncompatibility(5,3);}
							if(marker5RadioButton_6.isSelected()) {removeIncompatibility(5,4);}
							if(marker7RadioButton_6.isSelected()) {removeIncompatibility(5,6);}
						}
						if(numOfMarkers>6) {
							if(marker2RadioButton_7.isSelected()) {removeIncompatibility(6,1);}
							if(marker3RadioButton_7.isSelected()) {removeIncompatibility(6,2);}
							if(marker4RadioButton_7.isSelected()) {removeIncompatibility(6,3);}
							if(marker5RadioButton_7.isSelected()) {removeIncompatibility(6,4);}
							if(marker6RadioButton_7.isSelected()) {removeIncompatibility(6,5);}
						}
						saveNucleiIdentification(markerFolder+currentSegmentationFile.split("\\.")[0]+".tiff");
						
						if(measurementsBatchProcess) {
							markerMeasurements(measurementsFolder+currentSegmentationFile.split("\\.")[0]+".txt");
						}
						
					}
				}
			}
		}
	}
	/** batch process markers */ 
	private void batchMeasurements(int mode)
	{
		imageFolder = "Null";
		segmentationFolder = "Null";
		markerFolder = "Null";
		measurementsFolder = "Null";

		/** JButton for batch processing */
		JButton imageFolderButton = new JButton("Image folder");
		JButton segmentationFolderButton = new JButton("Segmentation folder");
		JButton markerFolderButton = new JButton("Marker folder");
		JButton measurementsFolderButton = new JButton("Measurements folder");

		JTextArea imageFolderQuestion = new JTextArea("Where is the folder with the input images?");
		JTextArea segmentationFolderQuestion = new JTextArea("Where is the folder with the segmented input images?");
		JTextArea markerFolderQuestion = new JTextArea("Where is the folder with the marker images?");
		JTextArea measurmentsFolderQuestion = new JTextArea("Where is the destination folder for the measurements?");
		imageFolderQuestion.setEditable(false);
		segmentationFolderQuestion.setEditable(false);
		markerFolderQuestion.setEditable(false);
		measurmentsFolderQuestion.setEditable(false);
		
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
		batchPanel.add(markerFolderQuestion,batchPanelConstraints);
		batchPanelConstraints.gridx++;
		batchPanel.add(markerFolderButton,batchPanelConstraints);
		batchPanelConstraints.gridy++;
		batchPanelConstraints.gridx=0;
		batchPanel.add(measurmentsFolderQuestion,batchPanelConstraints);
		batchPanelConstraints.gridx++;
		batchPanel.add(measurementsFolderButton,batchPanelConstraints);
		batchPanelConstraints.gridy++;

		GenericDialogPlus gd = new GenericDialogPlus("Batch processing for measurements");
		gd.addComponent(batchPanel);

		imageFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser imageChooser = new DirectoryChooser("Input images folder");
				imageFolder = imageChooser.getDirectory();
			}
		});

		segmentationFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser segmentationChooser = new DirectoryChooser("Segmentation images folder");
				segmentationFolder = segmentationChooser.getDirectory();
			}
		});
		markerFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser markerChooser = new DirectoryChooser("Marker images folder");
				markerFolder = markerChooser.getDirectory();
			}
		});
		measurementsFolderButton.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent arg0) {
				DirectoryChooser measurementsChooser = new DirectoryChooser("Measurements folder");
				measurementsFolder = measurementsChooser.getDirectory();
			}
		});

		gd.showDialog();

		if (gd.wasCanceled()) {
			for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
			for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
			for( ActionListener al : markerFolderButton.getActionListeners() ) {markerFolderButton.removeActionListener( al );}
			for( ActionListener al : measurementsFolderButton.getActionListeners() ) {measurementsFolderButton.removeActionListener( al );}
			return;
		}

		if (gd.wasOKed()) {
			for( ActionListener al : imageFolderButton.getActionListeners() ) {imageFolderButton.removeActionListener( al );}
			for( ActionListener al : segmentationFolderButton.getActionListeners() ) {segmentationFolderButton.removeActionListener( al );}
			for( ActionListener al : markerFolderButton.getActionListeners() ) {markerFolderButton.removeActionListener( al );}
			for( ActionListener al : measurementsFolderButton.getActionListeners() ) {measurementsFolderButton.removeActionListener( al );}
			if(imageFolder=="Null") {
				IJ.showMessage("You need to define a folder with the input images to process.");
				return;
			}
			if(segmentationFolder=="Null") {
				IJ.showMessage("You need to define a folder with the segmented input images to process.");
				return;
			}
			if(markerFolder=="Null") {
				IJ.showMessage("You need to define a folder with the marker images associated with the input images to process.");
				return;
			}
			if(measurementsFolder=="Null") {
				IJ.showMessage("You need to define a destination folder for the measurements.");
				return;
			}
			File imageFile = new File(imageFolder), segmentationFile = new File(segmentationFolder), markerFile = new File(markerFolder), measurementsFile = new File(measurementsFolder);
			for (File imageFileEntry : imageFile.listFiles()) {
				if (!imageFileEntry.isDirectory()) {
					String[] currentImageFile = imageFileEntry.getName().split("\\.");
					boolean ok1=false, ok2=false;
					for (File segmentationFileEntry : segmentationFile.listFiles()) {
						String[] currentSegmentationFile = segmentationFileEntry.getName().split("\\.");
						if(currentSegmentationFile[0].equals(currentImageFile[0])) {ok1=true;}
					}
					for (File markerFileEntry : markerFile.listFiles()) {
						String[] markerSegmentationFile = markerFileEntry.getName().split("\\.");
						if(markerSegmentationFile[0].equals(currentImageFile[0])) {ok2=true;}
					}
					if(!ok1 || !ok2) {
						IJ.showMessage("For each input image in the input image folder, there must be a segmentation image with the same name in the segmentation folder and a marker image with the same name in the marker folder.");
						return;
					}
				}
			}


			for (File imageFileEntry : imageFile.listFiles()) {
				if (!imageFileEntry.isDirectory()) {
					String[] currentImageFile = imageFileEntry.getName().split("\\.");
					String currentSegmentationFile = new String(), currentMarkerFile = new String();
					for (File segmentationFileEntry : segmentationFile.listFiles()) {
						String[] currentSegmentationFileTest = segmentationFileEntry.getName().split("\\.");
						if(currentSegmentationFileTest[0].equals(currentImageFile[0])) {currentSegmentationFile = segmentationFileEntry.getName();}
					}
					for (File markerFileEntry : markerFile.listFiles()) {
						String[] currentmarkerFileTest = markerFileEntry.getName().split("\\.");
						if(currentmarkerFileTest[0].equals(currentImageFile[0])) {currentMarkerFile = markerFileEntry.getName();}
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

					ImagePlus segmentedImage = opener.openImage(segmentationFolder+currentSegmentationFile);
					loadNucleiSegmentations(segmentedImage);

					ImagePlus markerImage = opener.openImage(markerFolder+currentMarkerFile);
					loadMarkerIdentifications(markerImage);

					if(mode==0) {classMeasurements(measurementsFolder+currentSegmentationFile.split("\\.")[0]+".txt");}
					else {markerMeasurements(measurementsFolder+currentSegmentationFile.split("\\.")[0]+".txt");}
					
				}
			}
		}
	}
	/** ask user to set intensity thresholding */ 
	private boolean addIntensityThresholdingWindow()
	{
		/** buttons */
		JTextArea intensityThresholdQuestion = new JTextArea("What is the intensity threshold?");
		intensityThresholdQuestion.setEditable(false);
		JTextArea intensityThresholdTextField = new JTextArea();
		intensityThresholdTextField.setText("" + intensityThresholdingScrollBar.getValue());
		
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
		if(threshold>intensityThresholdingScrollBar.getMaximum()) {
			IJ.showMessage("The threshold must be inferior than the maximum intensity");
			return false;}
		
		intensityThresholdingScrollBar.setValue(threshold);
		intensityThresholdingTextArea.setText("" + threshold);
		thresholdForMarker[numOfMarkers-1][1] = threshold;
		
		return true;
	}
	/** ask user to set intensity thresholding */ 
	private boolean addAreaThresholdingWindow()
	{
		/** buttons */
		JTextArea areaThresholdQuestion = new JTextArea("What is the area threshold (%)?");
		areaThresholdQuestion.setEditable(false);
		JTextArea areaThresholdTextField = new JTextArea();
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
		
		GenericDialogPlus gd = new GenericDialogPlus("Area threshold");
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
		thresholdForMarker[numOfMarkers-1][0] = threshold;
		
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
		
	private List<Point> drawNewObjectContour(int[] xPointsInit, int[] yPointsInit, int classId)
	{
		List<Point> ptsToRemove = new ArrayList<Point>();
		
		PointRoi pr = new PointRoi(xPointsInit, yPointsInit, xPointsInit.length);
		ShapeRoi roi = new ShapeRoi(pr);
		
		// add the roi to the overlay
		roi.setStrokeColor(colors[classColors[classId]]);
		overlay.add(roi);
		markersOverlay.add(roi );
		
		/*long  Time1 = System.currentTimeMillis();
		// list of points to remove corresponding to isolated points from the rest of the nucleus
		// also use this as a flag flag to tell the program if the nucleus has been created or not, when the shape of the nucleus cannot be recapitulated with a contour (at least with my limited criteria :)
		List<Point> ptsToRemove = new ArrayList<Point>();
		// find points on the right and bottom to be added as the roi lines only goes throught top right corners
		// first, identify pixels on the right and bottom border of the nucleus
		// then add pixels at these locations, just for visualization in the overlay
		int[] nbNeighborsRight = new int[xPointsInit.length],nbNeighborsBottom = new int[xPointsInit.length],nbNeighborsBottomRight = new int[xPointsInit.length];
		for (int u=0; u<xPointsInit.length; u++) {
			for (int v=0; v<xPointsInit.length; v++) {
				if(v!=u) {
					if(((xPointsInit[u]-xPointsInit[v])==(-1))&&(yPointsInit[u]==yPointsInit[v])){
						nbNeighborsRight[u]++;
					}
					if((xPointsInit[u]==xPointsInit[v])&&((yPointsInit[u]-yPointsInit[v])==-1)){
						nbNeighborsBottom[u]++;
					}
					if(((xPointsInit[u]-xPointsInit[v])==(-1))&&((yPointsInit[u]-yPointsInit[v])==-1)){
						nbNeighborsBottomRight[u]++;
					}
				}
			}
		}
		int nbNeighborsToAdd=0;
		List<Point> ptsToAdd = new ArrayList<Point>();
		for (int u=0; u<xPointsInit.length; u++) {
			if(nbNeighborsRight[u]==0) {
				boolean ptToAdd = true;
				for(int i=0;i<ptsToAdd.size();i++) {
					if((ptsToAdd.get(i).x==(xPointsInit[u]+1))&&(ptsToAdd.get(i).y==(yPointsInit[u]))) {
						ptToAdd = false;
					}
				}
				if(ptToAdd) {
					nbNeighborsToAdd++;
					Point pt = new Point(xPointsInit[u]+1,yPointsInit[u]);
					ptsToAdd.add(pt);
				}
			}
			if(nbNeighborsBottom[u]==0) {
				boolean ptToAdd = true;
				for(int i=0;i<ptsToAdd.size();i++) {
					if((ptsToAdd.get(i).x==(xPointsInit[u]))&&(ptsToAdd.get(i).y==(yPointsInit[u]+1))) {
						ptToAdd = false;
					}
				}
				if(ptToAdd) {
					nbNeighborsToAdd++;
					Point pt = new Point(xPointsInit[u],yPointsInit[u]+1);
					ptsToAdd.add(pt);
				}
			}
			if(nbNeighborsBottomRight[u]==0) {
				boolean ptToAdd = true;
				for(int i=0;i<ptsToAdd.size();i++) {
					if((ptsToAdd.get(i).x==(xPointsInit[u]+1))&&(ptsToAdd.get(i).y==(yPointsInit[u]+1))) {
						ptToAdd = false;
					}
				}
				if(ptToAdd) {
					nbNeighborsToAdd++;
					Point pt = new Point(xPointsInit[u]+1,yPointsInit[u]+1);
					ptsToAdd.add(pt);
				}
			}
		}
		long  Time2 = System.currentTimeMillis();
		// initialization of the nucleus region as the points in the nucleus plus the pixels to be added for visualization
		int[] xPoints = new int[xPointsInit.length+nbNeighborsToAdd], yPoints = new int[xPointsInit.length+nbNeighborsToAdd];
		int currentIndex=0;
		for (int u=0; u<xPointsInit.length; u++) {
			xPoints[currentIndex] = xPointsInit[u];
			yPoints[currentIndex] = yPointsInit[u];
			currentIndex++;
		}
		for (int u=0; u<ptsToAdd.size(); u++) {
			xPoints[currentIndex] = ptsToAdd.get(u).x;
			yPoints[currentIndex] = ptsToAdd.get(u).y;
			currentIndex++;
		}
		int[] nbNeighbors = new int[xPoints.length];
		for (int u=0; u<xPoints.length; u++) {
			for (int v=(u+1); v<xPoints.length; v++) {
				if(java.lang.Math.sqrt(java.lang.Math.pow(xPoints[u]-xPoints[v],2.)+java.lang.Math.pow(yPoints[u]-yPoints[v],2.))<(1.5)){
					nbNeighbors[u]++;
					nbNeighbors[v]++;
				}
			}
		}
		// count the number of points that are part of the nucleus outline
		// extract all nucleus points to initialize the roi via wand at the end with the median inside point
		int originalNbPtsOutline=0;
		int[] insideXvalues = new int[xPoints.length],insideYvalues = new int[xPoints.length];
		for (int u=0; u<xPoints.length; u++) {
			insideXvalues[u] = xPoints[u];
			insideYvalues[u] = yPoints[u];
			if((nbNeighbors[u]<8)&&(nbNeighbors[u]>2)) {
				originalNbPtsOutline++;
			}
			if(nbNeighbors[u]==1){
				Point pt = new Point(xPoints[u],yPoints[u]);
				ptsToRemove.add(pt);
			}
		}
		Arrays.sort(insideXvalues);
		Arrays.sort(insideYvalues);

		Point insidePt = new Point(insideXvalues[xPoints.length/2],insideYvalues[xPoints.length/2]);
		// find a path for each point around the nucleus so it can correctly initialize a roi
		// do a loop in case the path finds itself in a cul-de-sac so a different initilization might do the job, or a point removed in small loop might help out 
		boolean keepComputing=true;
		double multiplier=0;
		long  Time3 = System.currentTimeMillis();
		while(keepComputing) {
			// get points part of the nucleus outline
			int[] xPointsOutline = new int[originalNbPtsOutline];
			int[] yPointsOutline = new int[originalNbPtsOutline];
			// definition over two loops if we define a different initialization
			int nbPtsOutline=0;
			for (int u=(int)(xPoints.length*multiplier); u<xPoints.length; u++) {
				if((nbNeighbors[u]<8)&&(nbNeighbors[u]>2)) {
					xPointsOutline[nbPtsOutline] = xPoints[u];
					yPointsOutline[nbPtsOutline] = yPoints[u];
					nbPtsOutline++;
				}
			}
			for (int u=0; u<(int)(xPoints.length*multiplier); u++) {
				if((nbNeighbors[u]<8)&&(nbNeighbors[u]>2)) {
					xPointsOutline[nbPtsOutline] = xPoints[u];
					yPointsOutline[nbPtsOutline] = yPoints[u];
					nbPtsOutline++;
				}
			}
			// if a path was not found earlier, the small loops consisiting of 4 pixels next to each other as a small square are altered so one pixel in the loop is removed
			// we try the 4 different possibilities (top left, top right, bottom left, bottom right)
			if(multiplier>0) {
				List<Point> outlinePts = new ArrayList<Point>();
				int[] indexesToRemove = new int[nbPtsOutline];
				int nbPtsToRemove = 0;
				for(int u=0;u<xPointsOutline.length;u++) {
					Point pt = new Point(xPointsOutline[u],yPointsOutline[u]);
					outlinePts.add(pt);
				}
				if(multiplier<0.3) {
					for(int u=0;u<outlinePts.size();u++) {
						for(int v=0;v<outlinePts.size();v++) {
							if(((outlinePts.get(v).x)==(outlinePts.get(u).x+1))&&((outlinePts.get(v).y)==(outlinePts.get(u).y))) {
								for(int w=0;w<outlinePts.size();w++) {
									if(((outlinePts.get(w).x)==(outlinePts.get(u).x))&&((outlinePts.get(w).y)==(outlinePts.get(u).y+1))) {
										for(int z=0;z<outlinePts.size();z++) {
											if(((outlinePts.get(z).x)==(outlinePts.get(u).x+1))&&((outlinePts.get(z).y)==(outlinePts.get(u).y+1))) {
												indexesToRemove[u] = 1;
												nbPtsToRemove++;
											}
										}
									}
								}
							}
						}
					}
				}
				else {
					if(multiplier<0.6) {
						for(int u=0;u<outlinePts.size();u++) {
							for(int v=0;v<outlinePts.size();v++) {
								if(((outlinePts.get(v).x)==(outlinePts.get(u).x+1))&&((outlinePts.get(v).y)==(outlinePts.get(u).y))) {
									for(int w=0;w<outlinePts.size();w++) {
										if(((outlinePts.get(w).x)==(outlinePts.get(u).x))&&((outlinePts.get(w).y)==(outlinePts.get(u).y-1))) {
											for(int z=0;z<outlinePts.size();z++) {
												if(((outlinePts.get(z).x)==(outlinePts.get(u).x+1))&&((outlinePts.get(z).y)==(outlinePts.get(u).y-1))) {
													indexesToRemove[u] = 1;
													nbPtsToRemove++;
												}
											}
										}
									}
								}
							}
						}
					}
					else {
						if(multiplier<0.8) {
							for(int u=0;u<outlinePts.size();u++) {
								for(int v=0;v<outlinePts.size();v++) {
									if(((outlinePts.get(v).x)==(outlinePts.get(u).x-1))&&((outlinePts.get(v).y)==(outlinePts.get(u).y))) {
										for(int w=0;w<outlinePts.size();w++) {
											if(((outlinePts.get(w).x)==(outlinePts.get(u).x))&&((outlinePts.get(w).y)==(outlinePts.get(u).y+1))) {
												for(int z=0;z<outlinePts.size();z++) {
													if(((outlinePts.get(z).x)==(outlinePts.get(u).x-1))&&((outlinePts.get(z).y)==(outlinePts.get(u).y+1))) {
														indexesToRemove[u] = 1;
														nbPtsToRemove++;
													}
												}
											}
										}
									}
								}
							}
						}
						else {
							for(int u=0;u<outlinePts.size();u++) {
								for(int v=0;v<outlinePts.size();v++) {
									if(((outlinePts.get(v).x)==(outlinePts.get(u).x-1))&&((outlinePts.get(v).y)==(outlinePts.get(u).y))) {
										for(int w=0;w<outlinePts.size();w++) {
											if(((outlinePts.get(w).x)==(outlinePts.get(u).x))&&((outlinePts.get(w).y)==(outlinePts.get(u).y-1))) {
												for(int z=0;z<outlinePts.size();z++) {
													if(((outlinePts.get(z).x)==(outlinePts.get(u).x-1))&&((outlinePts.get(z).y)==(outlinePts.get(u).y-1))) {
														indexesToRemove[u] = 1;
														nbPtsToRemove++;
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
				// remove the pixels to be removed in the small 4-loops
				if(nbPtsToRemove>0){
					int[] xUpdatedPointsOutline = new int[nbPtsOutline-nbPtsToRemove];
					int[] yUpdatedPointsOutline = new int[nbPtsOutline-nbPtsToRemove];
					int index = 0;
					for(int u=0;u<nbPtsOutline;u++) {
						if(indexesToRemove[u]<1) {
							xUpdatedPointsOutline[index] = xPointsOutline[u];
							yUpdatedPointsOutline[index] = yPointsOutline[u];
							index++;
						}
					}
					nbPtsOutline = xUpdatedPointsOutline.length;
					xPointsOutline = null;
					yPointsOutline = null;
					xPointsOutline = new int[nbPtsOutline];
					yPointsOutline = new int[nbPtsOutline];
					for(int u=0;u<nbPtsOutline;u++) {
						xPointsOutline[u] = xUpdatedPointsOutline[u];
						yPointsOutline[u] = yUpdatedPointsOutline[u];
					}
				}
			}
			// sort the points in the nucleus outline in order to get nice polygon rois
			int[] xSortedPointsOutline = new int[nbPtsOutline];
			int[] ySortedPointsOutline = new int[nbPtsOutline];
			xSortedPointsOutline[0] = xPointsOutline[0];
			ySortedPointsOutline[0] = yPointsOutline[0];
			xPointsOutline[0] = -2;
			yPointsOutline[0] = -2;
			int refIndex = -1;
			double minDistance = 1.1;
			// start from point of index 0 and than find the closest point, point by point to finally get the path around the nucleus
			for (int u=1; u<nbPtsOutline; u++) {
				minDistance = 1.1;
				refIndex = -1;
				for (int v=1; v<nbPtsOutline; v++) {
					if(xPointsOutline[v]>(-1)) {
						double currentDistance = java.lang.Math.sqrt(java.lang.Math.pow(xSortedPointsOutline[u-1]-xPointsOutline[v],2.)+java.lang.Math.pow(ySortedPointsOutline[u-1]-yPointsOutline[v],2.));
						if(currentDistance<minDistance){
							refIndex = v;
						}
					}
				}
				if(refIndex>(-1)) {
					xSortedPointsOutline[u] = xPointsOutline[refIndex];
					ySortedPointsOutline[u] = yPointsOutline[refIndex];
					xPointsOutline[refIndex] = -2;
					yPointsOutline[refIndex] = -2;
				}
				else {
					minDistance = 1.5;
					for (int v=1; v<nbPtsOutline; v++) {
						if(xPointsOutline[v]>(-1)) {
							double currentDistance = java.lang.Math.sqrt(java.lang.Math.pow(xSortedPointsOutline[u-1]-xPointsOutline[v],2.)+java.lang.Math.pow(ySortedPointsOutline[u-1]-yPointsOutline[v],2.));
							if(currentDistance<minDistance){
								refIndex = v;
							}
						}
					}
					if(refIndex>(-1)) {
						xSortedPointsOutline[u] = xPointsOutline[refIndex];
						ySortedPointsOutline[u] = yPointsOutline[refIndex];
						xPointsOutline[refIndex] = -2;
						yPointsOutline[refIndex] = -2;
					}
				}
			}
			// find the maximum index that was put in the path
			int maxValidIndex=0;
			for (int u=0; u<nbPtsOutline; u++) {
				if((xSortedPointsOutline[u]>0.001)||(ySortedPointsOutline[u]>0.001)) {
					maxValidIndex = u;
				}
			}
			// define roi
			if(maxValidIndex<(nbPtsOutline-1)) {
				// all points were not matched to the path
				double distanceBetweenFirstandLastContourPts = java.lang.Math.sqrt(java.lang.Math.pow(xSortedPointsOutline[maxValidIndex]-xSortedPointsOutline[0],2.)+java.lang.Math.pow(ySortedPointsOutline[maxValidIndex]-ySortedPointsOutline[0],2.));
				// test if first and last points in the current path are neighbors 
				if((distanceBetweenFirstandLastContourPts<1.5)&&(maxValidIndex>(int)(9*(double)(nbPtsOutline)/10))) {
					// include the points that were not put in the path by finding the pair of points minimizing the distance when adding the point
					for (int u=0; u<nbPtsOutline; u++) {
						if(xPointsOutline[u]>(-1)) {
							int refIndexForMissingPt=0;
							double distanceSum = java.lang.Math.sqrt(java.lang.Math.pow(xSortedPointsOutline[maxValidIndex]-xPointsOutline[u],2.)+java.lang.Math.pow(ySortedPointsOutline[maxValidIndex]-yPointsOutline[u],2.)) +
									java.lang.Math.sqrt(java.lang.Math.pow(xSortedPointsOutline[0]-xPointsOutline[u],2.)+java.lang.Math.pow(ySortedPointsOutline[0]-yPointsOutline[u],2.));
							for (int v=1; v<maxValidIndex; v++) {
								double currentDistanceSum = java.lang.Math.sqrt(java.lang.Math.pow(xSortedPointsOutline[v-1]-xPointsOutline[u],2.)+java.lang.Math.pow(ySortedPointsOutline[v-1]-yPointsOutline[u],2.)) +
										java.lang.Math.sqrt(java.lang.Math.pow(xSortedPointsOutline[v]-xPointsOutline[u],2.)+java.lang.Math.pow(ySortedPointsOutline[v]-yPointsOutline[u],2.));
								if(currentDistanceSum<distanceSum) {
									distanceSum = currentDistanceSum;
									refIndexForMissingPt = v;
								}
							}
							for (int v=maxValidIndex+1; v>(refIndexForMissingPt); v--) {
								xSortedPointsOutline[v] = xSortedPointsOutline[v-1];
								ySortedPointsOutline[v] = ySortedPointsOutline[v-1];
							}
							maxValidIndex++;
							xSortedPointsOutline[refIndexForMissingPt] = xPointsOutline[u];
							ySortedPointsOutline[refIndexForMissingPt] = yPointsOutline[u];
							xPointsOutline[u] = -2;
							yPointsOutline[u] = -2;
						}
					}
					if((xSortedPointsOutline[nbPtsOutline-1]<0.001)&&(ySortedPointsOutline[nbPtsOutline-1]<0.001)) {
						for (int u=0; u<nbPtsOutline; u++) {
							IJ.log("index: " + u + ": " + xSortedPointsOutline[u] + ',' + ySortedPointsOutline[u]);
						}
					}
					// defines polygon roi associated with contour
					PolygonRoi fpRoi = new PolygonRoi(xSortedPointsOutline,ySortedPointsOutline,xSortedPointsOutline.length,Roi.FREEROI);
					ImageProcessor mask = fpRoi.getMask();
					double xMin = displayImage.getWidth(), xMax = 0, yMin = displayImage.getHeight(), yMax = 0;
					for(int u=0;u<xSortedPointsOutline.length;u++) {
						if(xSortedPointsOutline[u]<xMin) {
							xMin = xSortedPointsOutline[u];
						}
						if(ySortedPointsOutline[u]<yMin) {
							yMin = ySortedPointsOutline[u];
						}
						if(xSortedPointsOutline[u]>xMax) {
							xMax = xSortedPointsOutline[u];
						}
						if(ySortedPointsOutline[u]>yMax) {
							yMax = ySortedPointsOutline[u];
						}
					}
					// define roi from mask
					Wand w = new Wand(mask);
					w.autoOutline( insidePt.x-(int)xMin, insidePt.y-(int)yMin );
					Roi roi = null;
					if ( w.npoints > 0) {
						roi = new PolygonRoi( w.xpoints, w.ypoints, w.npoints, Roi.TRACED_ROI );
					}
					double mw = roi.getFloatWidth(), mh = roi.getFloatHeight();
					// if polygon roi and roi defined from mask do not have the same width and/or height => some points were removed and it might change the location of the nucleus
					if((mw<(xMax-xMin))||(mh<(yMax-yMin))) {
						// find mask contours
						int[] nbMaskNeighbors = new int[w.xpoints.length];
						for (int u=0; u<w.xpoints.length; u++) {
							for (int v=(u+1); v<w.xpoints.length; v++) {
								if(java.lang.Math.sqrt(java.lang.Math.pow(w.xpoints[u]-w.xpoints[v],2.)+java.lang.Math.pow(w.ypoints[u]-w.ypoints[v],2.))<(1.5)){
									nbMaskNeighbors[u]++;
									nbMaskNeighbors[v]++;
								}
							}
						}
						// count the number of points that are part of the nucleus outline
						int nbMaskPtsOutline=0;
						for (int u=0; u<w.xpoints.length; u++) {
							if(nbMaskNeighbors[u]<8) {
								nbMaskPtsOutline++;
							}
						}
						// get points part of the nucleus outline
						int[] xMaskPointsOutline = new int[nbMaskPtsOutline];
						int[] yMaskPointsOutline = new int[nbMaskPtsOutline];

						int maskIndex=0;
						for (int u=0; u<nbMaskPtsOutline; u++) {
							if(nbMaskNeighbors[u]<8) {
								xMaskPointsOutline[maskIndex] = w.xpoints[u];
								yMaskPointsOutline[maskIndex] = w.ypoints[u];
								maskIndex++;
							}
						}
						// define the most common points between mask contours and polygon contours with no translation, x translation, y translation and xy translation
						// update the location to translate the roi accordingly
						int nbCommonPtsNoShift=0, nbCommonPtsxShift=0, nbCommonPtsyShift=0, nbCommonPtsxyShift=0;
						for(int u=0;u<xSortedPointsOutline.length;u++) {
							for(int v=0;v<nbMaskPtsOutline;v++) {
								if((((int)xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v])&&(((int)ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v])) {
									nbCommonPtsNoShift++;
								}
								else {
									if((((int)xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v]+1)&&(((int)ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v])) {
										nbCommonPtsxShift++;
									}
									else {
										if((((int)xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v])&&(((int)ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v]+1)) {
											nbCommonPtsyShift++;
										}
										else {
											if((((int)xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v]+1)&&(((int)ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v]+1)) {
												nbCommonPtsxyShift++;
											}
										}
									}
								}
							}
						}
						if((nbCommonPtsxyShift>nbCommonPtsxShift)&&(nbCommonPtsxyShift>nbCommonPtsyShift)&&(nbCommonPtsxyShift>nbCommonPtsNoShift)) {
							xMin += 1;
							yMin += 1;
						}
						else {
							if((nbCommonPtsxShift>nbCommonPtsyShift)&&(nbCommonPtsxShift>nbCommonPtsNoShift)) {
								xMin += 1;
							}
							else {
								if(nbCommonPtsyShift>nbCommonPtsNoShift) {
									yMin += 1;
								}	
							}
						}
					}
					// add the roi to the overlay
					roi.setStrokeColor(colors[classColors[classId]]);
					roi.setLocation(Math.round(xMin), Math.round(yMin));
					overlay.add(roi);
					markersOverlay.add(roi );
					keepComputing = false;
				}
				else {
					// we did not find a correct path => change the initialization and points to remove to try to fins a correct path on the contour
					multiplier += 0.25;
					// after 4 tries, we give up and remove the nucleus
					if(multiplier>1.1) {
						ptsToRemove = null;
						ptsToRemove = new ArrayList<Point>();
						Point pt = new Point(-1,-1);
						ptsToRemove.add(pt);
						keepComputing = false;
					}
				}
			}
			else {
				// defines polygon roi associated with contour
				PolygonRoi fpRoi = new PolygonRoi(xSortedPointsOutline,ySortedPointsOutline,xSortedPointsOutline.length,Roi.FREEROI);
				ImageProcessor mask = fpRoi.getMask();
				ImageStatistics stats = mask.getStatistics();
				double xMin = displayImage.getWidth(), xMax = 0, yMin = displayImage.getHeight(), yMax = 0;
				for(int u=0;u<xSortedPointsOutline.length;u++) {
					if(xSortedPointsOutline[u]<xMin) {
						xMin = xSortedPointsOutline[u];
					}
					if(ySortedPointsOutline[u]<yMin) {
						yMin = ySortedPointsOutline[u];
					}
					if(xSortedPointsOutline[u]>xMax) {
						xMax = xSortedPointsOutline[u];
					}
					if(ySortedPointsOutline[u]>yMax) {
						yMax = ySortedPointsOutline[u];
					}
				}
				// define roi from mask
				Wand w = new Wand(mask);
				w.autoOutline( insidePt.x-(int)xMin, insidePt.y-(int)yMin );
				Roi roi = null;
				if ( w.npoints > 0) {
					roi = new PolygonRoi( w.xpoints, w.ypoints, w.npoints, Roi.TRACED_ROI );
				}
				if(w.npoints==0) {
					ptsToRemove = null;
					ptsToRemove = new ArrayList<Point>();
					Point pt = new Point(-1,-1);
					ptsToRemove.add(pt);
					return ptsToRemove;
				}
				double mw = roi.getFloatWidth(), mh = roi.getFloatHeight();
				// if polygon roi and roi defined from mask do not have the same width and/or height => some points were removed and it might change the location of the nucleus
				if((mw<(xMax-xMin))||(mh<(yMax-yMin))) {
					// find mask contours
					int[] nbMaskNeighbors = new int[w.xpoints.length];
					for (int u=0; u<w.xpoints.length; u++) {
						for (int v=(u+1); v<w.xpoints.length; v++) {
							if(java.lang.Math.sqrt(java.lang.Math.pow(w.xpoints[u]-w.xpoints[v],2.)+java.lang.Math.pow(w.ypoints[u]-w.ypoints[v],2.))<(1.5)){
								nbMaskNeighbors[u]++;
								nbMaskNeighbors[v]++;
							}
						}
					}
					// count the number of points that are part of the nucleus outline
					int nbMaskPtsOutline=0;
					for (int u=0; u<w.xpoints.length; u++) {
						if(nbMaskNeighbors[u]<8) {
							nbMaskPtsOutline++;
						}
					}
					// get points part of the nucleus outline
					int[] xMaskPointsOutline = new int[nbMaskPtsOutline];
					int[] yMaskPointsOutline = new int[nbMaskPtsOutline];

					int maskIndex=0;
					for (int u=0; u<nbMaskPtsOutline; u++) {
						if(nbMaskNeighbors[u]<8) {
							xMaskPointsOutline[maskIndex] = w.xpoints[u];
							yMaskPointsOutline[maskIndex] = w.ypoints[u];
							maskIndex++;
						}
					}					
					// define the most common points between mask contours and polygon contours with no translation, x translation, y translation and xy translation
					// update the location to translate the roi accordingly
					int nbCommonPtsNoShift=0, nbCommonPtsxShift=0, nbCommonPtsyShift=0, nbCommonPtsxyShift=0;
					for(int u=0;u<xSortedPointsOutline.length;u++) {
						for(int v=0;v<nbMaskPtsOutline;v++) {
							if(((xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v])&&((ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v])) {
								nbCommonPtsNoShift++;
							}
							else {
								if(((xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v]+1)&&((ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v])) {
									nbCommonPtsxShift++;
								}
								else {
									if(((xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v])&&((ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v]+1)) {
										nbCommonPtsyShift++;
									}
									else {
										if(((xSortedPointsOutline[u]-xMin)==xMaskPointsOutline[v]+1)&&((ySortedPointsOutline[u]-yMin)==yMaskPointsOutline[v]+1)) {
											nbCommonPtsxyShift++;
										}
									}
								}
							}
						}
					}
					if((nbCommonPtsxyShift>nbCommonPtsxShift)&&(nbCommonPtsxyShift>nbCommonPtsyShift)&&(nbCommonPtsxyShift>nbCommonPtsNoShift)) {
						xMin += 1;
						yMin += 1;
					}
					else {
						if((nbCommonPtsxShift>nbCommonPtsyShift)&&(nbCommonPtsxShift>nbCommonPtsNoShift)) {
							xMin += 1;
						}
						else {
							if(nbCommonPtsyShift>nbCommonPtsNoShift) {
								yMin += 1;
							}	
						}
					}
				}
				// add the roi to the overlay
				roi.setStrokeColor(colors[classColors[classId]]);
				roi.setLocation(Math.round(xMin), Math.round(yMin));
				overlay.add(roi);
				markersOverlay.add(roi );
				keepComputing = false;
			}
		}*/
		long  Time4 = System.currentTimeMillis();
		/*IJ.log("First interval: " + (Time2-Time1));
		IJ.log("Secondinterval: " + (Time3-Time2));
		IJ.log("Third interval: " + (Time4-Time3));*/
		return ptsToRemove;
	}
	
	/**
	 * Remove objects
	 */
	private void removeRoi(int classId, int roiId, int overlayId)
	{
		objectsInEachClass[classId].remove(roiId);
		for(byte j=0;j<numOfMarkers;j++) {
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
							List<Point> ptsToRemove = drawNewObjectContour(xPoints,yPoints,firstObjectToMerge_class);
							if(ptsToRemove.size()>0) {
								// remove points that have no neighbors
								// if point has coordinates -1,-1 => this nucleus has to be removed
								if(ptsToRemove.get(0).x!=(-1)) {
									int [] pointsToRemoveIndexes = new int[xPoints.length];
									int nbPointsToRemove=0;
									for(int i=0;i<ptsToRemove.size();i++) {
										for(int u = 0; u< xPoints.length; u++) {
											if(((int)xPoints[u]==ptsToRemove.get(i).x)&&((int)yPoints[u]==ptsToRemove.get(i).y)) {
												pointsToRemoveIndexes[u] = 1;
												nbPointsToRemove++;
											}
										}
									}
									int[] xUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
									int[] yUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
									int currentIndex=0;
									for(int u = 0; u< xPoints.length; u++) {
										if(pointsToRemoveIndexes[u]<1) {
											xUpdatedPoints[currentIndex] = xPoints[u];
											yUpdatedPoints[currentIndex] = yPoints[u];
											currentIndex++;
										}
									}
									xPoints = null;
									yPoints = null;
									xPoints = xUpdatedPoints;
									yPoints = yUpdatedPoints;
								
									// add nucleus to the list of nuclei
									Point[] roiPoints = new Point[xPoints.length];
									for(int u = 0; u< xPoints.length; u++) {
										roiFlag[xPoints[u]][yPoints[u]][0] = firstObjectToMerge_class;
										roiFlag[xPoints[u]][yPoints[u]][1] = (short)objectsInEachClass[firstObjectToMerge_class].size();
										roiFlag[xPoints[u]][yPoints[u]][2] = (short)(overlay.size()-1);
										roiPoints[u] = new Point(xPoints[u],yPoints[u]);
									}
									// define polygon and roi corresponding to the new region
									//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
									// save new nucleus as roi in the corresponding class
									objectsInEachClass[firstObjectToMerge_class].add(roiPoints);
								}
							}
							else {
								// add nucleus to the list of nuclei
								Point[] roiPoints = new Point[xPoints.length];
								for(int u = 0; u< xPoints.length; u++) {
									roiFlag[xPoints[u]][yPoints[u]][0] = firstObjectToMerge_class;
									roiFlag[xPoints[u]][yPoints[u]][1] = (short)objectsInEachClass[firstObjectToMerge_class].size();
									roiFlag[xPoints[u]][yPoints[u]][2] = (short)(overlay.size()-1);
									roiPoints[u] = new Point(xPoints[u],yPoints[u]);
								}
								// define polygon and roi corresponding to the new region
								//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
								// save new nucleus as roi in the corresponding class
								objectsInEachClass[firstObjectToMerge_class].add(roiPoints);
							}

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
		displayImage.killRoi();
		Point[] pts = r.getContainedPoints();
		/*IJ.showMessage("Pt 0: " + pts[0].x + ',' + pts[0].y + ": " + roiFlag[pts[0].x][pts[0].y][2] + "   Pt 1: " + pts[pts.length-1].x + ',' + pts[pts.length-1].y + ": " + roiFlag[pts[pts.length-1].x][pts[pts.length-1].y][2]);
		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int[] outputArray = new int[displayImage.getWidth()*displayImage.getHeight()];
		for(int y=0;y<displayImage.getHeight();y++) {
			for(int x=0;x<displayImage.getHeight();x++) {
				outputArray[y*displayImage.getWidth()+x] = roiFlag[x][y][2];
			}
		}
		stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), outputArray));
		ImagePlus test = new ImagePlus("test", stack);
		test.show();*/
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
					// copy rois to merge
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
					
					List<Point> r1 = new ArrayList<Point>();
					neighbor2D(rp[0].x, rp[0].y, nucleusImage, flag, r1, displayImage.getDimensions()[0], displayImage.getDimensions()[1]);
					
					int[] xPoints1 = new int[r1.size()];
					int[] yPoints1 = new int[r1.size()];
					for(int u=0;u<r1.size();u++) {
						xPoints1[u] = r1.get(u).x;
						yPoints1[u] = r1.get(u).y;
					}
					
					// update display
					List<Point> ptsToRemove1 = drawNewObjectContour(xPoints1,yPoints1,nucleusClass);
					if(ptsToRemove1.size()>0) {
						// remove points that have no neighbors
						// if point has coordinates -1,-1 => this nucleus has to be removed
						if(ptsToRemove1.get(0).x!=(-1)) {
							int [] pointsToRemoveIndexes = new int[xPoints1.length];
							int nbPointsToRemove1=0;
							for(int i=0;i<ptsToRemove1.size();i++) {
								for(int u = 0; u< xPoints1.length; u++) {
									if(((int)xPoints1[u]==ptsToRemove1.get(i).x)&&((int)yPoints1[u]==ptsToRemove1.get(i).y)) {
										pointsToRemoveIndexes[u] = 1;
										nbPointsToRemove1++;
									}
								}
							}
							int[] xUpdatedPoints = new int[xPoints1.length-nbPointsToRemove1];
							int[] yUpdatedPoints = new int[xPoints1.length-nbPointsToRemove1];
							int currentIndex=0;
							for(int u = 0; u< xPoints1.length; u++) {
								if(pointsToRemoveIndexes[u]<1) {
									xUpdatedPoints[currentIndex] = xPoints1[u];
									yUpdatedPoints[currentIndex] = yPoints1[u];
									currentIndex++;
								}
							}
							xPoints1 = null;
							yPoints1 = null;
							xPoints1 = xUpdatedPoints;
							yPoints1 = yUpdatedPoints;
						
							// add nucleus to the list of nuclei
							Point[] roiPoints = new Point[xPoints1.length];
							for(int u = 0; u< xPoints1.length; u++) {
								roiFlag[xPoints1[u]][yPoints1[u]][0] = nucleusClass;
								roiFlag[xPoints1[u]][yPoints1[u]][1] = (short)objectsInEachClass[nucleusClass].size();
								roiFlag[xPoints1[u]][yPoints1[u]][2] = (short)(overlay.size()-1);
								originalNucleusImage[xPoints1[u]][yPoints1[u]] = overlay.size()-1;
								roiPoints[u] = new Point(xPoints1[u],yPoints1[u]);
							}
							// define polygon and roi corresponding to the new region
							PolygonRoi fPoly = new PolygonRoi(xPoints1,yPoints1,xPoints1.length,Roi.FREEROI);
							// save new nucleus as roi in the corresponding class
							objectsInEachClass[nucleusClass].add(roiPoints);
						}
					}
					else {
						// add nucleus to the list of nuclei
						Point[] roiPoints = new Point[xPoints1.length];
						for(int u = 0; u< xPoints1.length; u++) {
							roiFlag[xPoints1[u]][yPoints1[u]][0] = nucleusClass;
							roiFlag[xPoints1[u]][yPoints1[u]][1] = (short)objectsInEachClass[nucleusClass].size();
							roiFlag[xPoints1[u]][yPoints1[u]][2] = (short)(overlay.size()-1);
							originalNucleusImage[xPoints1[u]][yPoints1[u]] = overlay.size()-1;
							roiPoints[u] = new Point(xPoints1[u],yPoints1[u]);
						}
						// define polygon and roi corresponding to the new region
						//PolygonRoi fPoly = new PolygonRoi(xPoints1,yPoints1,xPoints1.length,Roi.FREEROI);
						// save new nucleus as roi in the corresponding class
						objectsInEachClass[nucleusClass].add(roiPoints);
					}
					
					// second object
					int firstPtInLineX = -1, firstPtInLineY = -1;
					for(int u=0;u<pts.length;u++) {
						if(originalNucleusImage[pts[u].x][pts[u].y]>0) {
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
					List<Point> ptsToRemove2 = drawNewObjectContour(xPoints2,yPoints2,nucleusClass);
					if(ptsToRemove2.size()>0) {
						// remove points that have no neighbors
						// if point has coordinates -1,-1 => this nucleus has to be removed
						if(ptsToRemove2.get(0).x!=(-1)) {
							int [] pointsToRemoveIndexes = new int[xPoints2.length];
							int nbPointsToRemove2=0;
							for(int i=0;i<ptsToRemove2.size();i++) {
								for(int u = 0; u< xPoints2.length; u++) {
									if(((int)xPoints2[u]==ptsToRemove2.get(i).x)&&((int)yPoints2[u]==ptsToRemove2.get(i).y)) {
										pointsToRemoveIndexes[u] = 1;
										nbPointsToRemove2++;
									}
								}
							}
							int[] xUpdatedPoints = new int[xPoints2.length-nbPointsToRemove2];
							int[] yUpdatedPoints = new int[xPoints2.length-nbPointsToRemove2];
							int currentIndex=0;
							for(int u = 0; u< xPoints2.length; u++) {
								if(pointsToRemoveIndexes[u]<1) {
									xUpdatedPoints[currentIndex] = xPoints2[u];
									yUpdatedPoints[currentIndex] = yPoints2[u];
									currentIndex++;
								}
							}
							xPoints2 = null;
							yPoints2 = null;
							xPoints2 = xUpdatedPoints;
							yPoints2 = yUpdatedPoints;
						
							// add nucleus to the list of nuclei
							Point[] roiPoints = new Point[xPoints2.length];
							for(int u = 0; u< xPoints2.length; u++) {
								roiFlag[xPoints2[u]][yPoints2[u]][0] = nucleusClass;
								roiFlag[xPoints2[u]][yPoints2[u]][1] = (short)objectsInEachClass[nucleusClass].size();
								roiFlag[xPoints2[u]][yPoints2[u]][2] = (short)(overlay.size()-1);
								roiPoints[u] = new Point(xPoints2[u],yPoints2[u]);
							}
							// define polygon and roi corresponding to the new region
							//PolygonRoi fPoly = new PolygonRoi(xPoints2,yPoints2,xPoints2.length,Roi.FREEROI);
							// save new nucleus as roi in the corresponding class
							objectsInEachClass[nucleusClass].add(roiPoints);
						}
					}
					else {
						// add nucleus to the list of nuclei
						Point[] roiPoints = new Point[xPoints2.length];
						for(int u = 0; u< xPoints2.length; u++) {
							roiFlag[xPoints2[u]][yPoints2[u]][0] = nucleusClass;
							roiFlag[xPoints2[u]][yPoints2[u]][1] = (short)objectsInEachClass[nucleusClass].size();
							roiFlag[xPoints2[u]][yPoints2[u]][2] = (short)(overlay.size()-1);
							roiPoints[u] = new Point(xPoints2[u],yPoints2[u]);
						}
						// define polygon and roi corresponding to the new region
						//PolygonRoi fPoly = new PolygonRoi(xPoints2,yPoints2,xPoints2.length,Roi.FREEROI);
						// save new nucleus as roi in the corresponding class
						objectsInEachClass[nucleusClass].add(roiPoints);
					}
					
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
	 * Swap object class
	 */
	private void swapObjectClass(Point[] objectToSwap, byte newClass)
	{
		if(roiFlag[objectToSwap[objectToSwap.length/2].x][objectToSwap[objectToSwap.length/2].y][0]!=newClass) {
			int objectCurrentClass = roiFlag[objectToSwap[objectToSwap.length/2].x][objectToSwap[objectToSwap.length/2].y][0], 
					objectClassId = roiFlag[objectToSwap[objectToSwap.length/2].x][objectToSwap[objectToSwap.length/2].y][1], 
					objectOverlayId = roiFlag[objectToSwap[objectToSwap.length/2].x][objectToSwap[objectToSwap.length/2].y][2];
			// duplicate object coordinates
			int [] newRoiX = new int[objectToSwap.length], newRoiY = new int[objectToSwap.length];
			Point[] roiPoints = new Point[objectToSwap.length];
			for(int u = 0; u< objectToSwap.length; u++) {
				newRoiX[u] = objectToSwap[u].x;
				newRoiY[u] = objectToSwap[u].y;
				roiFlag[newRoiX[u]][newRoiY[u]][0] = newClass;
				roiFlag[newRoiX[u]][newRoiY[u]][1] = (short)objectsInEachClass[newClass].size();
				roiFlag[newRoiX[u]][newRoiY[u]][2] = (short)overlay.size();
				roiPoints[u] = new Point(newRoiX[u],newRoiY[u]);
			}
			removeRoi(objectCurrentClass, objectClassId, objectOverlayId);
			//PolygonRoi fPoly = new PolygonRoi(newRoiX,newRoiY,newRoiX.length,Roi.FREEROI);
			// save new nucleus as roi in the corresponding class
			objectsInEachClass[newClass].add(roiPoints);
			drawNewObjectContour(newRoiX, newRoiY, newClass);
		}
	}
	/**
	 * Annotate nuclei markers
	 */
	void activateNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[markerColors[currentMarker][currentPattern]]);
				markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(2);
				positiveNucleiForEachMarker[currentMarker][currentPattern].add(roiFlag[pt.x][pt.y][2]);
			}
		}
	}
	void deactivateNucleusMarker(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				if(markersOverlay.get(roiFlag[pt.x][pt.y][2]).getStrokeColor()==(colors[markerColors[currentMarker][currentPattern]])) {
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[classColors[roiFlag[pt.x][pt.y][0]]]);
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(0);
					for(int i = 0; i < positiveNucleiForEachMarker[currentMarker][currentPattern].size(); i++) {
						if(positiveNucleiForEachMarker[currentMarker][currentPattern].get(i)==roiFlag[pt.x][pt.y][2]) {
							positiveNucleiForEachMarker[currentMarker][currentPattern].remove(i);
						}
					}
				}
				else {
					for(int k=0;k<4;k++) {
						if(k!= currentPattern) {
							for(int i = 0; i < positiveNucleiForEachMarker[currentMarker][k].size(); i++) {
								if(positiveNucleiForEachMarker[currentMarker][k].get(i)==roiFlag[pt.x][pt.y][2]) {
									positiveNucleiForEachMarker[currentMarker][k].remove(i);
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
		if(currentMarker>(-1)) {
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
	 * Annotate nuclei markers with thresholding
	 */
	void activateNucleusMarkerThresholding(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				if(markersOverlay.get(roiFlag[pt.x][pt.y][2]).getStrokeWidth()==0) {
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[markerColors[currentMarker][currentPattern]]);
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(2);
					positiveNucleiForEachMarker[currentMarker][currentPattern].add(roiFlag[pt.x][pt.y][2]);
				}
			}
		}
	}
	void deactivateNucleusMarkerThresholding(Point pt)
	{
		if((pt.x>(-1)) && (pt.y>(-1))){
			if(roiFlag[pt.x][pt.y][2]>(-1)) {
				if(markersOverlay.get(roiFlag[pt.x][pt.y][2]).getStrokeColor()==(colors[markerColors[currentMarker][currentPattern]])) {
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeColor(colors[classColors[roiFlag[pt.x][pt.y][0]]]);
					markersOverlay.get(roiFlag[pt.x][pt.y][2]).setStrokeWidth(0);
					for(int i = 0; i < positiveNucleiForEachMarker[currentMarker][currentPattern].size(); i++) {
						if(positiveNucleiForEachMarker[currentMarker][currentPattern].get(i)==roiFlag[pt.x][pt.y][2]) {
							positiveNucleiForEachMarker[currentMarker][currentPattern].remove(i);
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
			Toolbar.getInstance().setTool(Toolbar.POINT);
		}
		else if(pressedButton==2) {
			newObjectButton.setSelected(false);
			removeObjectButton.setSelected(false);
			mergeObjectsButton.setSelected(true);
			splitObjectsButton.setSelected(false);
			swapObjectClassButton.setSelected(false);
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
			displayFlag = 0;

			nucleiAnnotationButton.setSelected(true);
			nucleiMarkerButton.setSelected(false);
			currentMode = 0;
			removeMarkersFromOverlay();
			currentMarker = -1;
			displayImage.updateAndDraw();
		}
		else if(pressedButton==1) {
			initializeVisualizeChannelButtons2();
			visualizeAllChannelsButton1.setSelected(true);
			displayFlag = 0;
			
			nucleiAnnotationButton.setSelected(false);
			nucleiMarkerButton.setSelected(true);
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
		SwingUtilities.invokeLater(
				new Runnable() {
					public void run() {
						win = new CustomWindow(displayImage);
						win.pack();
					}
				});
		
		// refresh overlay
		if(currentMode==0) {
			IJ.wait(100);
			displayImage.setOverlay(overlay);
			displayImage.updateAndDraw();
		}
		else {
			IJ.wait(150);
			displayImage.setOverlay(markersOverlay);
			displayImage.updateAndDraw();
		}
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
		}
		else {
			if(pressedButton==1) {
				class1Button.setSelected(false);
				class2Button.setSelected(true);
				class3Button.setSelected(false);
				class4Button.setSelected(false);
				class5Button.setSelected(false);
				currentClass = 1;
			}
			else {
				if(pressedButton==2) {
					class1Button.setSelected(false);
					class2Button.setSelected(false);
					class3Button.setSelected(true);
					class4Button.setSelected(false);
					class5Button.setSelected(false);
					currentClass = 2;
				}
				else {
					if(pressedButton==3) {
						class1Button.setSelected(false);
						class2Button.setSelected(false);
						class3Button.setSelected(false);
						class4Button.setSelected(true);
						class5Button.setSelected(false);
						currentClass = 3;
					}
					else {
						if(pressedButton==4) {
							class1Button.setSelected(false);
							class2Button.setSelected(false);
							class3Button.setSelected(false);
							class4Button.setSelected(false);
							class5Button.setSelected(true);
							currentClass = 4;
						}
					}
				}
			}
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
	
	
	/**
	 * Update analyze channels buttons as only one channel can be annotated at once
	 */
	void initializeMarkerButtons() {
		marker1Button.setSelected(false);
		marker1Pattern1Button.setSelected(false);
		marker1Pattern2Button.setSelected(false);
		marker1Pattern3Button.setSelected(false);
		marker1Pattern4Button.setSelected(false);
		marker2Button.setSelected(false);
		marker2Pattern1Button.setSelected(false);
		marker2Pattern2Button.setSelected(false);
		marker2Pattern3Button.setSelected(false);
		marker2Pattern4Button.setSelected(false);
		marker3Button.setSelected(false);
		marker3Pattern1Button.setSelected(false);
		marker3Pattern2Button.setSelected(false);
		marker3Pattern3Button.setSelected(false);
		marker3Pattern4Button.setSelected(false);
		marker4Button.setSelected(false);
		marker4Pattern1Button.setSelected(false);
		marker4Pattern2Button.setSelected(false);
		marker4Pattern3Button.setSelected(false);
		marker4Pattern4Button.setSelected(false);
		marker5Button.setSelected(false);
		marker5Pattern1Button.setSelected(false);
		marker5Pattern2Button.setSelected(false);
		marker5Pattern3Button.setSelected(false);
		marker5Pattern4Button.setSelected(false);
		marker6Button.setSelected(false);
		marker6Pattern1Button.setSelected(false);
		marker6Pattern2Button.setSelected(false);
		marker6Pattern3Button.setSelected(false);
		marker6Pattern4Button.setSelected(false);
		marker7Button.setSelected(false);
		marker7Pattern1Button.setSelected(false);
		marker7Pattern2Button.setSelected(false);
		marker7Pattern3Button.setSelected(false);
		marker7Pattern4Button.setSelected(false);
	}
	void removeCurrentNucleiMarkerOverlays() {
		for(int p=0;p<4;p++) {
			for(int i = 0; i < positiveNucleiForEachMarker[currentMarker][p].size(); i++) {
				Point[] pts = overlay.get(positiveNucleiForEachMarker[currentMarker][p].get(i)).getContainedPoints();
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
	void activateCurrentNucleiMarkerOverlays(int marker) {
		for(int i = 0; i < positiveNucleiForEachMarker[marker][0].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][0].get(i)).setStrokeColor(colors[markerColors[marker][0]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][0].get(i)).setStrokeWidth(2);
		}
		for(int i = 0; i < positiveNucleiForEachMarker[marker][1].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][1].get(i)).setStrokeColor(colors[markerColors[marker][1]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][1].get(i)).setStrokeWidth(2);
		}
		for(int i = 0; i < positiveNucleiForEachMarker[marker][2].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][2].get(i)).setStrokeColor(colors[markerColors[marker][2]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][2].get(i)).setStrokeWidth(2);
		}
		for(int i = 0; i < positiveNucleiForEachMarker[marker][3].size(); i++) {
			markersOverlay.get(positiveNucleiForEachMarker[marker][3].get(i)).setStrokeColor(colors[markerColors[marker][3]]);
			markersOverlay.get(positiveNucleiForEachMarker[marker][3].get(i)).setStrokeWidth(2);
		}
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
	}
	void updateAnnotateMarker(int pressedButton)
	{
		if(pressedButton==0) {
			initializeMarkerButtons();
			marker1Button.setSelected(true);
			marker1Pattern1Button.setSelected(true);
			if(currentMarker!=0) {
				if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
				currentMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(0);
			}
		}
		else if(pressedButton==1) {
			initializeMarkerButtons();
			marker2Button.setSelected(true);
			marker2Pattern1Button.setSelected(true);
			if(currentMarker!=1) {
				if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
				currentMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(1);
			}
		}
		else if(pressedButton==2) {
			initializeMarkerButtons();
			marker3Button.setSelected(true);
			marker3Pattern1Button.setSelected(true);
			if(currentMarker!=2) {
				if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
				currentMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(2);
			}
		}
		else if(pressedButton==3) {
			initializeMarkerButtons();
			marker4Button.setSelected(true);
			marker4Pattern1Button.setSelected(true);
			if(currentMarker!=3) {
				if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
				currentMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(3);
			}
		}
		else if(pressedButton==4) {
			initializeMarkerButtons();
			marker5Button.setSelected(true);
			marker5Pattern1Button.setSelected(true);
			if(currentMarker!=4) {
				if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
				currentMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(4);
			}
		}
		else if(pressedButton==5) {
			initializeMarkerButtons();
			marker6Button.setSelected(true);
			marker6Pattern1Button.setSelected(true);
			if(currentMarker!=5) {
				if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
				currentMarker = pressedButton;
				currentPattern = 0;
				activateCurrentNucleiMarkerOverlays(5);
			}
		}
		else if(pressedButton==6) {
			initializeMarkerButtons();
			marker7Button.setSelected(true);
			marker7Pattern1Button.setSelected(true);
			if(currentMarker!=6) {
				if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
				currentMarker = pressedButton;
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
		if(currentMarker>(-1)) {
			if(((currentMarker*4)<=pressedButton)&&(((currentMarker+1)*4)>pressedButton)) {
				if(pressedButton==0) {
					initializeMarkerButtons();
					marker1Button.setSelected(true);
					marker1Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==1) {
					initializeMarkerButtons();
					marker1Button.setSelected(true);
					marker1Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==2) {
					initializeMarkerButtons();
					marker1Button.setSelected(true);
					marker1Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==3) {
					initializeMarkerButtons();
					marker1Button.setSelected(true);
					marker1Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==4) {
					initializeMarkerButtons();
					marker2Button.setSelected(true);
					marker2Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==5) {
					initializeMarkerButtons();
					marker2Button.setSelected(true);
					marker2Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==6) {
					initializeMarkerButtons();
					marker2Button.setSelected(true);
					marker2Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==7) {
					initializeMarkerButtons();
					marker2Button.setSelected(true);
					marker2Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==8) {
					initializeMarkerButtons();
					marker3Button.setSelected(true);
					marker3Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==9) {
					initializeMarkerButtons();
					marker3Button.setSelected(true);
					marker3Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==10) {
					initializeMarkerButtons();
					marker3Button.setSelected(true);
					marker3Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==11) {
					initializeMarkerButtons();
					marker3Button.setSelected(true);
					marker3Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==12) {
					initializeMarkerButtons();
					marker4Button.setSelected(true);
					marker4Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==13) {
					initializeMarkerButtons();
					marker4Button.setSelected(true);
					marker4Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==14) {
					initializeMarkerButtons();
					marker4Button.setSelected(true);
					marker4Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==15) {
					initializeMarkerButtons();
					marker4Button.setSelected(true);
					marker4Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==16) {
					initializeMarkerButtons();
					marker5Button.setSelected(true);
					marker5Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==17) {
					initializeMarkerButtons();
					marker5Button.setSelected(true);
					marker5Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==18) {
					initializeMarkerButtons();
					marker5Button.setSelected(true);
					marker5Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==19) {
					initializeMarkerButtons();
					marker5Button.setSelected(true);
					marker5Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==20) {
					initializeMarkerButtons();
					marker6Button.setSelected(true);
					marker6Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==21) {
					initializeMarkerButtons();
					marker6Button.setSelected(true);
					marker6Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==22) {
					initializeMarkerButtons();
					marker6Button.setSelected(true);
					marker6Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==23) {
					initializeMarkerButtons();
					marker6Button.setSelected(true);
					marker6Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
				else if(pressedButton==24) {
					initializeMarkerButtons();
					marker7Button.setSelected(true);
					marker7Pattern1Button.setSelected(true);
					currentPattern = 0;
				}
				else if(pressedButton==25) {
					initializeMarkerButtons();
					marker7Button.setSelected(true);
					marker7Pattern2Button.setSelected(true);
					currentPattern = 1;
				}
				else if(pressedButton==26) {
					initializeMarkerButtons();
					marker7Button.setSelected(true);
					marker7Pattern3Button.setSelected(true);
					currentPattern = 2;
				}
				else if(pressedButton==27) {
					initializeMarkerButtons();
					marker7Button.setSelected(true);
					marker7Pattern4Button.setSelected(true);
					currentPattern = 3;
				}
			}
			else {
				initializeMarkerButtons();
				if(currentMarker==0) {
					marker1Button.setSelected(true);
					if(currentPattern==0) {
						marker1Pattern1Button.setSelected(true);
					}
					else if(currentPattern==1) {
						marker1Pattern2Button.setSelected(true);
					}
					else if(currentPattern==2) {
						marker1Pattern3Button.setSelected(true);
					}
					else if(currentPattern==3) {
						marker1Pattern4Button.setSelected(true);
					}
				}
				if(currentMarker==1) {
					marker2Button.setSelected(true);
					if(currentPattern==0) {
						marker2Pattern1Button.setSelected(true);
					}
					else if(currentPattern==1) {
						marker2Pattern2Button.setSelected(true);
					}
					else if(currentPattern==2) {
						marker2Pattern3Button.setSelected(true);
					}
					else if(currentPattern==3) {
						marker2Pattern4Button.setSelected(true);
					}
				}
				if(currentMarker==2) {
					marker3Button.setSelected(true);
					if(currentPattern==0) {
						marker3Pattern1Button.setSelected(true);
					}
					else if(currentPattern==1) {
						marker3Pattern2Button.setSelected(true);
					}
					else if(currentPattern==2) {
						marker3Pattern3Button.setSelected(true);
					}
					else if(currentPattern==3) {
						marker3Pattern4Button.setSelected(true);
					}
				}
				if(currentMarker==3) {
					marker4Button.setSelected(true);
					if(currentPattern==0) {
						marker4Pattern1Button.setSelected(true);
					}
					else if(currentPattern==1) {
						marker4Pattern2Button.setSelected(true);
					}
					else if(currentPattern==2) {
						marker4Pattern3Button.setSelected(true);
					}
					else if(currentPattern==3) {
						marker4Pattern4Button.setSelected(true);
					}
				}
				if(currentMarker==4) {
					marker5Button.setSelected(true);
					if(currentPattern==0) {
						marker5Pattern1Button.setSelected(true);
					}
					else if(currentPattern==1) {
						marker5Pattern2Button.setSelected(true);
					}
					else if(currentPattern==2) {
						marker5Pattern3Button.setSelected(true);
					}
					else if(currentPattern==3) {
						marker5Pattern4Button.setSelected(true);
					}
				}
				if(currentMarker==5) {
					marker6Button.setSelected(true);
					if(currentPattern==0) {
						marker6Pattern1Button.setSelected(true);
					}
					else if(currentPattern==1) {
						marker6Pattern2Button.setSelected(true);
					}
					else if(currentPattern==2) {
						marker6Pattern3Button.setSelected(true);
					}
					else if(currentPattern==3) {
						marker6Pattern4Button.setSelected(true);
					}
				}
				if(currentMarker==6) {
					marker7Button.setSelected(true);
					if(currentPattern==0) {
						marker7Pattern1Button.setSelected(true);
					}
					else if(currentPattern==1) {
						marker7Pattern2Button.setSelected(true);
					}
					else if(currentPattern==2) {
						marker7Pattern3Button.setSelected(true);
					}
					else if(currentPattern==3) {
						marker7Pattern4Button.setSelected(true);
					}
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
		// make sure the user wants to remove the class
		switch ( JOptionPane.showConfirmDialog( null, "Are you sure you want to remove class " + (classToRemove+1) + "?", "Class removal", JOptionPane.YES_NO_OPTION ) )
		{
		case JOptionPane.YES_OPTION:
			// remove nuclei belonging to the class to remove
			int progressIndex=0, totalNbObjectsToRemove=objectsInEachClass[classToRemove].size();
			while(objectsInEachClass[classToRemove].size()>0) {
				IJ.showProgress(progressIndex, totalNbObjectsToRemove);
				//Polygon pl = objectsInEachClass[classToRemove].get(0).getPolygon();
				Point[] pl = objectsInEachClass[classToRemove].get(0);
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
				SwingUtilities.invokeLater(
						new Runnable() {
							public void run() {
								win = new CustomWindow(displayImage);
								win.pack();
							}
						});
			}
			else {
				// reinitializa class 1
				objectsInEachClass[0] = null;
				objectsInEachClass[0] = new ArrayList<Point[]>();
			}

			// display update
			IJ.wait(150);
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
	private boolean updateRoiColorWindow(int roiClass)
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
		
		
		switch (markerColors[marker][0]) {
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
		switch (markerColors[marker][1]) {
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
		switch (markerColors[marker][2]) {
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
		switch (markerColors[marker][3]) {
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
	 * Add new marker in the panel
	 */
	private boolean addNewMarker() 
	{
		if(numOfMarkers == MAX_NUM_MARKERS)
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
	 * Remove marker
	 */
	private void deleteMarker(int markerToRemove) {
		// remove marker identifications belonging to the marker to remove for each pattern
		initializeMarkerButtons();
		if(currentMarker>(-1)) {removeCurrentNucleiMarkerOverlays();}
		for(int p=0;p<4;p++) {
			while(positiveNucleiForEachMarker[markerToRemove][p].size()>0) {
				positiveNucleiForEachMarker[markerToRemove][p].remove(0);
			}
		}
		// update number of markers
		numOfMarkers--;
		
		// if marker to remove is not the last one, all of the markers after the marker to remove change id -> -1
		for(int i=markerToRemove;i<numOfMarkers;i++) {
			// copy marker i+1 to marker i
			for(int p=0;p<4;p++) {
				for(int j=0;j<positiveNucleiForEachMarker[i+1][p].size();j++) {
					positiveNucleiForEachMarker[i][p].add(positiveNucleiForEachMarker[i+1][p].get(j));
				}
				markerColors[i][p] = markerColors[i+1][p];
				markerCellcompartment[i] = markerCellcompartment[i+1];
				channelForMarker[i] = channelForMarker[i+1];
				thresholdForMarker[i][0] = thresholdForMarker[i+1][0];
				thresholdForMarker[i][1] = thresholdForMarker[i+1][1];
			}
			// delete marker i+1
			for(int p=0;p<4;p++) {
				while(positiveNucleiForEachMarker[i+1][p].size()>0) {
					positiveNucleiForEachMarker[i+1][p].remove(0);
				}
			}
		}
		
		// remove action listener for last class
		switch (numOfMarkers) {
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
			markerColors[numOfMarkers][p] = (byte)(p+4);
		}
		markerCellcompartment[numOfMarkers] = 0;
		channelForMarker[numOfMarkers] = -1;
		thresholdForMarker[numOfMarkers][0] = -1;
		thresholdForMarker[numOfMarkers][1] = -1;
		currentMarker = -1;
		currentPattern = -1;
		
		// update panel (one class less)
		//Build GUI
		SwingUtilities.invokeLater(
				new Runnable() {
					public void run() {
						win = new CustomWindow(displayImage);
						win.pack();
					}
				});
		
		IJ.wait(150);
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
	}
	private void removeMarker(int markerToRemove)
	{
		// make sure the user wants to remove the marker
		switch ( JOptionPane.showConfirmDialog( null, "Are you sure you want to remove marker " + (markerToRemove+1) + "?", "Marker removal", JOptionPane.YES_NO_OPTION ) )
		{
		case JOptionPane.YES_OPTION:
			deleteMarker(markerToRemove);
			break;
		case JOptionPane.NO_OPTION:
			return;
		}
	}	
		
	/**
	 * Summarize all info
	 */
	private void classMeasurements() 
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			RoiManager rm = new RoiManager();
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
					rm.addRoi(sr);
				}
			}
			
			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}
			ResultsTable rt = rm.multiMeasure(displayImage);
			rm.close();
			
			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt.getValueAsDouble(k, 0), value2 = rt.getValueAsDouble(k, 1);
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
							finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1), rt.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1)+"Ch"+(c+1), rt.getValueAsDouble(rtIndex, c));
							}
							rtIndex++;
						}
					}
					finalRt.addValue("Class", i+1);
					//Polygon pl = objectsInEachClass[i].get(j).getPolygon();
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];
				}
			}
			finalRt.show("Results");
		}
	}
	private void classMeasurements(String outputPath) 
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			RoiManager rm = new RoiManager();
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
					rm.addRoi(sr);
				}
			}
			
			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}
			ResultsTable rt = rm.multiMeasure(displayImage);
			rm.close();
			
			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt.getValueAsDouble(k, 0), value2 = rt.getValueAsDouble(k, 1);
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
							finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1), rt.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1)+"Ch"+(c+1), rt.getValueAsDouble(rtIndex, c));
							}
							rtIndex++;
						}
					}
					finalRt.addValue("Class", i+1);
					//Polygon pl = objectsInEachClass[i].get(j).getPolygon();
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];
				}
			}
			finalRt.save(outputPath);
		}
	}
	/**
	 * Summarize info for one single nucleus
	 */
	private void classMeasurementsForOneNucleus() 
	{
		//get selected region
		Roi r = displayImage.getRoi();
		if (null == r){
			return;
		}
		displayImage.killRoi();
			
		Point[] pts = r.getContainedPoints();
		if(roiFlag[pts[0].x][pts[0].y][0]>(-1)) {
			RoiManager rm = new RoiManager();
			Point[] nucleusToMeasure = objectsInEachClass[roiFlag[pts[0].x][pts[0].y][0]].get(roiFlag[pts[0].x][pts[0].y][1]);
			int[] xPts = new int[nucleusToMeasure.length], yPts = new int[nucleusToMeasure.length];
			for(int p=0;p<xPts.length;p++) {
				xPts[p] = nucleusToMeasure[p].x;
				yPts[p] = nucleusToMeasure[p].y;
			}
			PointRoi pr = new PointRoi(xPts, yPts, xPts.length);
			ShapeRoi sr = new ShapeRoi(pr);
			overlay.add(sr);
			rm.addRoi(sr);
			ResultsTable rt = rm.multiMeasure(displayImage);
			rm.close();
			
			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt.getValueAsDouble(k, 0), value2 = rt.getValueAsDouble(k, 1);
				if(value2!=value1) {
					intensityFeatures[k] = 1;
				}
			}

			final ResultsTable finalRt = new ResultsTable();
			finalRt.incrementCounter();
			int rtIndex=0;
			for(int k=0;k<nbFeatures;k++) {
				if(intensityFeatures[k]==0) {
					finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1), rt.getValueAsDouble(rtIndex, 0));
					rtIndex++;
				}
				else {
					for(int c=0;c<numOfChannels;c++) {
						finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1)+"Ch"+(c+1), rt.getValueAsDouble(rtIndex, c));
					}
					rtIndex++;
				}
			}
			finalRt.addValue("Class", 1);
			IJ.log("Size: " + xPts.length);
			finalRt.show("Results");
			
			ImageProcessor mask = sr!=null?sr.getMask():null;
			ImagePlus currentImage = new ImagePlus("Roi", mask) ;
			currentImage.show();
			
		}
	}
	/** ask user to define parameters for nuclei filtering */ 
	private boolean addFilterWindow()
	{
		/** buttons for marker characterization */
		JTextArea minNbPixelsPerNucleusQuestion = new JTextArea("What is the minimum number of pixels per nucleus?");
		minNbPixelsPerNucleusQuestion.setEditable(false);
		JTextField minNbPixelsPerNucleusTextField = new JTextField();
		minNbPixelsPerNucleusTextField.setText("" + 50);
		JTextArea minMinorOverMajorRatioQuestion = new JTextArea("What is the minimum accepted ratio between the minor and major axis of an ellipse fitting the nucleus?");
		minMinorOverMajorRatioQuestion.setEditable(false);
		JTextField minMinorOverMajorRatioTextField = new JTextField();
		minMinorOverMajorRatioTextField.setText("" + 0.5);
		
		JPanel filteringPanel = new JPanel();
		filteringPanel.setBorder(BorderFactory.createTitledBorder(""));
		GridBagLayout filteringPanelLayout = new GridBagLayout();
		GridBagConstraints filteringPanelConstraints = new GridBagConstraints();
		filteringPanelConstraints.anchor = GridBagConstraints.NORTHWEST;
		filteringPanelConstraints.fill = GridBagConstraints.HORIZONTAL;
		filteringPanelConstraints.gridwidth = 1;
		filteringPanelConstraints.gridheight = 1;
		filteringPanelConstraints.gridx = 0;
		filteringPanelConstraints.gridy = 0;
		filteringPanel.setLayout(filteringPanelLayout);
		
		filteringPanel.add(minNbPixelsPerNucleusQuestion,filteringPanelConstraints);
		filteringPanelConstraints.gridy++;
		minNbPixelsPerNucleusTextField.setPreferredSize( new Dimension( 50, 24 ) );
		filteringPanel.add(minNbPixelsPerNucleusTextField,filteringPanelConstraints);
		filteringPanelConstraints.gridy++;
		filteringPanel.add(minMinorOverMajorRatioQuestion,filteringPanelConstraints);
		filteringPanelConstraints.gridy++;
		minMinorOverMajorRatioTextField.setPreferredSize( new Dimension( 50, 24 ) );
		filteringPanel.add(minMinorOverMajorRatioTextField,filteringPanelConstraints);
		
		
		GenericDialogPlus gd = new GenericDialogPlus("Nuclei filtering");
		gd.addComponent(filteringPanel);
		gd.showDialog();

		if (gd.wasCanceled())
			return false;
		
		// update cell compartment marker status
		int minNbPixelsPerNucleus = Integer.valueOf(minNbPixelsPerNucleusTextField.getText());
		double minMinorOverMajorRatio = Double.valueOf(minMinorOverMajorRatioTextField.getText());
		filterNuclei(minNbPixelsPerNucleus, minMinorOverMajorRatio);
		
		return true;
	}
	/**
	 * Filter nuclei based on nuclei features
	 */
	private void filterNuclei(int minNbPixelsPerNucleus, double minMinorOverMajorRatio) 
	{
		// size filtering
		int totalNbObjects = 0, globalCurrentIndex = 0;
		for(int i=0;i<numOfClasses;i++) {
			totalNbObjects += objectsInEachClass[i].size();
		}
		byte newClass = numOfClasses;
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				IJ.showProgress(globalCurrentIndex, totalNbObjects);
				//Polygon currentRoi = objectsInEachClass[i].get(j).getPolygon();
				Point[] currentRoi = objectsInEachClass[i].get(j);
				if(currentRoi.length<minNbPixelsPerNucleus) {
					if(newClass>=numOfClasses) {addNewClass();}
					swapObjectClass(currentRoi, newClass);
				}
				globalCurrentIndex++;
			}
		}
		newClass = numOfClasses;
		// shape filtering
		globalCurrentIndex = 0;
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				IJ.showProgress(globalCurrentIndex, totalNbObjects);
				Point[] currentNucleus = objectsInEachClass[i].get(j);
				int[] xPts = new int[currentNucleus.length], yPts = new int[currentNucleus.length];
				for(int p=0;p<xPts.length;p++) {
					xPts[p] = currentNucleus[p].x;
					yPts[p] = currentNucleus[p].y;
				}
				PolygonRoi pr = new PolygonRoi(xPts, yPts, xPts.length, Roi.FREEROI);
				if(pr.getFloatWidth()<pr.getFloatHeight()) {
					if((pr.getFloatWidth()/pr.getFloatHeight())<minMinorOverMajorRatio) {
						if(newClass>=numOfClasses) {addNewClass();}
						swapObjectClass(currentNucleus, newClass);
					}
				}
				else {
					if((pr.getFloatHeight()/pr.getFloatWidth())<minMinorOverMajorRatio) {
						if(newClass>=numOfClasses) {addNewClass();}
						swapObjectClass(currentNucleus, newClass);
					}
				}
				globalCurrentIndex++;
			}
		}
		displayImage.updateAndDraw();
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
			RoiManager rm = new RoiManager();
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
					rm.addRoi(sr);
				}
			}
			
			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}
			ResultsTable rt = rm.multiMeasure(displayImage);
			rm.close();
			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt.getValueAsDouble(k, 0), value2 = rt.getValueAsDouble(k, 1);
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
							finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1), rt.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1)+"Ch"+(c+1), rt.getValueAsDouble(rtIndex, c));
							}
							rtIndex++;
						}
					}
					finalRt.addValue("Class", i+1);
					//Polygon pl = objectsInEachClass[i].get(j).getPolygon();
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];

					for(int k=0;k<numOfMarkers;k++) {
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
	private void markerMeasurements(String outputPath) 
	{
		if(objectsInEachClass[0].size()==0) {
			IJ.showMessage("No object", "There are no annotated objects");
		}
		else {
			RoiManager rm = new RoiManager();
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
					rm.addRoi(sr);
				}
			}
			
			int nbObjects=0;
			for(int i=0;i<numOfClasses;i++) {
				nbObjects += objectsInEachClass[i].size();
			}
			ResultsTable rt = rm.multiMeasure(displayImage);
			rm.close();
			int nbCols=0;
			for  (int cnt=0;cnt<10000000; cnt++) {
				if (rt.columnExists(cnt)){
					nbCols++;
				}
			}
			int nbFeatures = nbCols/nbObjects;
			int[] intensityFeatures = new int[nbFeatures];
			for(int k=0;k<nbFeatures;k++) {
				double value1 = rt.getValueAsDouble(k, 0), value2 = rt.getValueAsDouble(k, 1);
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
							finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1), rt.getValueAsDouble(rtIndex, 0));
							rtIndex++;
						}
						else {
							for(int c=0;c<numOfChannels;c++) {
								finalRt.addValue(rt.getColumnHeading(k).substring(0, rt.getColumnHeading(k).length() - 1)+"Ch"+(c+1), rt.getValueAsDouble(rtIndex, c));
							}
							rtIndex++;
						}
					}
					finalRt.addValue("Class", i+1);
					//Polygon pl = objectsInEachClass[i].get(j).getPolygon();
					Point[] pl = objectsInEachClass[i].get(j);
					int overlayId = roiFlag[pl[pl.length/2].x][pl[pl.length/2].y][2];

					for(int k=0;k<numOfMarkers;k++) {
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
			finalRt.save(outputPath);
		}
	}
	/** illustration of markers wrt to identified objects */
	void takeMarkerSnapshot() {
		initializeMarkerButtons();
		removeMarkersFromOverlay();
		displayImage.updateAndDraw();
		currentMarker = -1;
		
		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int[][][] nuclearComponent = computeNuclearComponent(), membranarComponent = computeMembranarComponent(nuclearComponent), cytoplasmicComponent = computeCytoplasmicComponent(nuclearComponent, membranarComponent);
		List<FloatPolygon> [] nuclearComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], membranarComponentInEachClass = new ArrayList[MAX_NUM_CLASSES], cytoplasmicComponentInEachClass = new ArrayList[MAX_NUM_CLASSES];

		for(int i=0;i<numOfClasses;i++) {
			nuclearComponentInEachClass[i] = new ArrayList<FloatPolygon>();
			membranarComponentInEachClass[i] = new ArrayList<FloatPolygon>();
			cytoplasmicComponentInEachClass[i] = new ArrayList<FloatPolygon>();
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int j=0;j<objectsInEachClass[i].size();j++) {
				FloatPolygon fp1 = new FloatPolygon(), fp2 = new FloatPolygon(), fp3 = new FloatPolygon();
				nuclearComponentInEachClass[i].add(fp1);
				membranarComponentInEachClass[i].add(fp2);
				cytoplasmicComponentInEachClass[i].add(fp3);
			}
		}
		for(int i=0;i<numOfClasses;i++) {
			for(int y=0;y<displayImage.getHeight();y++) {
				for(int x=0;x<displayImage.getWidth();x++) {
					if(nuclearComponent[i][x][y]>0) {
						nuclearComponentInEachClass[i].get(nuclearComponent[i][x][y]-1).addPoint(x, y);
					}
					if(membranarComponent[i][x][y]>0) {
						membranarComponentInEachClass[i].get(membranarComponent[i][x][y]-1).addPoint(x, y);
					}
					if(cytoplasmicComponent[i][x][y]>0) {
						cytoplasmicComponentInEachClass[i].get(cytoplasmicComponent[i][x][y]-1).addPoint(x, y);
					}
				}
			}
		}
		for(int k=0;k<numOfMarkers;k++) {
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
						}
					}
					else if(markerCellcompartment[k]==1) {
						FloatPolygon fp = membranarComponentInEachClass[currentClass].get(currentObject);
						for(int l=0;l<fp.npoints;l++) {
							outputArray[(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
						}
					}
					else if(markerCellcompartment[k]==2) {
						FloatPolygon fp = cytoplasmicComponentInEachClass[currentClass].get(currentObject);
						for(int l=0;l<fp.npoints;l++) {
							outputArray[(int)fp.ypoints[l]*displayImage.getWidth()+(int)fp.xpoints[l]] = 255; 
						}
					}
				}
			}
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), outputArray));
		}
		
		ImagePlus marker = new ImagePlus("Marker visualization", stack);
		marker = HyperStackConverter.toHyperStack(marker, numOfMarkers, 1, 1);
		marker.setOverlay(overlay);
		marker.show();

	}
	/**
	 * update class color
	 */
	private void updateClassColor() {
		overlay = new Overlay();
		markersOverlay = new Overlay();
		for(int c=0;c<numOfClasses;c++) {
			for(int r=0;r<objectsInEachClass[c].size();r++) {
				//Polygon pl = objectsInEachClass[c].get(r).getPolygon();
				Point[] pl = objectsInEachClass[c].get(r);
				int[] xPoints = new int[pl.length], yPoints = new int[pl.length];
				for(int i=0;i<pl.length;i++) {
					xPoints[i] = pl[i].x;
					yPoints[i] = pl[i].y;
				}
				drawNewObjectContour(xPoints,yPoints,c);
			}
		}
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();
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
				SwingUtilities.invokeLater(
						new Runnable() {
							public void run() {
								win = new CustomWindow(displayImage);
								win.pack();
							}
						});
			}
			// nuclei markers
			for(int i = 0; i < numOfMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			numOfMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					markerColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				channelForMarker[i] = -1;
				thresholdForMarker[i][0] = -1;
				thresholdForMarker[i][1] = -1;
			}
			removeMarker1ButtonFromListener();
			removeMarker2ButtonFromListener();
			removeMarker3ButtonFromListener();
			removeMarker4ButtonFromListener();
			removeMarker5ButtonFromListener();
			removeMarker6ButtonFromListener();
			removeMarker7ButtonFromListener();
			
			for(int i = 0; i < numOfMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = new ArrayList<Short>();
				}
			}
			for(byte c=0;c<stack.getSize();c++) {
				currentClass = c;
				ImageProcessor ip = stack.getProcessor(c+1);
				ImageStatistics roiStats = segmentedImage.getStatistics();
				double nbRois = roiStats.max;

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
							List<Point> ptsToRemove = drawNewObjectContour(xPoints,yPoints,currentClass);
							if(ptsToRemove.size()>0) {
								// remove points that have no neighbors
								// if point has coordinates -1,-1 => this nucleus has to be removed
								if(ptsToRemove.get(0).x!=(-1)) {
									int [] pointsToRemoveIndexes = new int[xPoints.length];
									int nbPointsToRemove=0;
									for(int p=0;p<ptsToRemove.size();p++) {
										for(int u = 0; u< xPoints.length; u++) {
											if(((int)xPoints[u]==ptsToRemove.get(p).x)&&((int)yPoints[u]==ptsToRemove.get(p).y)) {
												pointsToRemoveIndexes[u] = 1;
												nbPointsToRemove++;
											}
										}
									}
									int[] xUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
									int[] yUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
									int currentPtIndex=0;
									for(int u = 0; u< xPoints.length; u++) {
										if(pointsToRemoveIndexes[u]<1) {
											xUpdatedPoints[currentPtIndex] = xPoints[u];
											yUpdatedPoints[currentPtIndex] = yPoints[u];
											currentPtIndex++;
										}
									}
									xPoints = null;
									yPoints = null;
									xPoints = xUpdatedPoints;
									yPoints = yUpdatedPoints;
									// add nucleus to the list of nuclei
									Point[] roiPoints = new Point[xPoints.length];
									for(int u = 0; u< xPoints.length; u++) {
										roiFlag[(int)xPoints[u]][(int)yPoints[u]][0] = currentClass;
										roiFlag[(int)xPoints[u]][(int)yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
										roiFlag[(int)xPoints[u]][(int)yPoints[u]][2] = (short)(overlay.size()-1);
										roiPoints[u] = new Point(xPoints[u],yPoints[u]);
									}
									// define polygon and roi corresponding to the new region
									//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
									// save new nucleus as roi in the corresponding class
									objectsInEachClass[currentClass].add(roiPoints);
								}
							}
							else {
								// add nucleus to the list of nuclei
								Point[] roiPoints = new Point[xPoints.length];
								for(int u = 0; u< xPoints.length; u++) {
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][0] = currentClass;
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][2] = (short)(overlay.size()-1);
									roiPoints[u] = new Point(xPoints[u],yPoints[u]);
								}
								// define polygon and roi corresponding to the new region
								//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
								// save new nucleus as roi in the corresponding class
								objectsInEachClass[currentClass].add(roiPoints);
							}
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
				SwingUtilities.invokeLater(
						new Runnable() {
							public void run() {
								win = new CustomWindow(displayImage);
								win.pack();
							}
						});
			}
			// nuclei markers
			for(int i = 0; i < numOfMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			numOfMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					markerColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				channelForMarker[i] = -1;
				thresholdForMarker[i][0] = -1;
				thresholdForMarker[i][1] = -1;
			}
			removeMarker1ButtonFromListener();
			removeMarker2ButtonFromListener();
			removeMarker3ButtonFromListener();
			removeMarker4ButtonFromListener();
			removeMarker5ButtonFromListener();
			removeMarker6ButtonFromListener();
			removeMarker7ButtonFromListener();
			
			for(int i = 0; i < numOfMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = new ArrayList<Short>();
				}
			}
			for(byte c=0;c<stack.getSize();c++) {
				currentClass = c;
				ImageProcessor ip = stack.getProcessor(c+1);
				ImageStatistics roiStats = segmentedImage.getStatistics();
				double nbRois = roiStats.max;

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
							List<Point> ptsToRemove = drawNewObjectContour(xPoints,yPoints,currentClass);
							if(ptsToRemove.size()>0) {
								// remove points that have no neighbors
								// if point has coordinates -1,-1 => this nucleus has to be removed
								if(ptsToRemove.get(0).x!=(-1)) {
									int [] pointsToRemoveIndexes = new int[xPoints.length];
									int nbPointsToRemove=0;
									for(int p=0;p<ptsToRemove.size();p++) {
										for(int u = 0; u< xPoints.length; u++) {
											if(((int)xPoints[u]==ptsToRemove.get(p).x)&&((int)yPoints[u]==ptsToRemove.get(p).y)) {
												pointsToRemoveIndexes[u] = 1;
												nbPointsToRemove++;
											}
										}
									}
									int[] xUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
									int[] yUpdatedPoints = new int[xPoints.length-nbPointsToRemove];
									int currentPtIndex=0;
									for(int u = 0; u< xPoints.length; u++) {
										if(pointsToRemoveIndexes[u]<1) {
											xUpdatedPoints[currentPtIndex] = xPoints[u];
											yUpdatedPoints[currentPtIndex] = yPoints[u];
											currentPtIndex++;
										}
									}
									xPoints = null;
									yPoints = null;
									xPoints = xUpdatedPoints;
									yPoints = yUpdatedPoints;
									// add nucleus to the list of nuclei
									Point[] roiPoints = new Point[xPoints.length];
									for(int u = 0; u< xPoints.length; u++) {
										roiFlag[(int)xPoints[u]][(int)yPoints[u]][0] = currentClass;
										roiFlag[(int)xPoints[u]][(int)yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
										roiFlag[(int)xPoints[u]][(int)yPoints[u]][2] = (short)(overlay.size()-1);
										roiPoints[u] = new Point(xPoints[u],yPoints[u]);
									}
									// define polygon and roi corresponding to the new region
									//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
									// save new nucleus as roi in the corresponding class
									objectsInEachClass[currentClass].add(roiPoints);
								}
							}
							else {
								// add nucleus to the list of nuclei
								Point[] roiPoints = new Point[xPoints.length];
								for(int u = 0; u< xPoints.length; u++) {
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][0] = currentClass;
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][1] = (short)objectsInEachClass[currentClass].size();
									roiFlag[(int)xPoints[u]][(int)yPoints[u]][2] = (short)(overlay.size()-1);
									roiPoints[u] = new Point(xPoints[u],yPoints[u]);
								}
								// define polygon and roi corresponding to the new region
								//PolygonRoi fPoly = new PolygonRoi(xPoints,yPoints,xPoints.length,Roi.FREEROI);
								// save new nucleus as roi in the corresponding class
								objectsInEachClass[currentClass].add(roiPoints);
							}
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
		displayImage.setOverlay(overlay);
		displayImage.updateAndDraw();		
		segmentedImage = null;
	}
	
	/**
	 * load marker identification
	 */
	private void loadMarkerIdentifications() 
	{
		ImagePlus markerImage = IJ.openImage();
		if (null == markerImage) return; // user canceled open dialog
		else {

			ImageStack stack = markerImage.getStack();
			int[] markerDims = markerImage.getDimensions();
			
			// test on nuclei segmentation image dimensions
			if ((markerDims[2]>1)&&(markerDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((markerDims[2]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((markerDims[3]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((markerDims[0]!=displayImage.getWidth())||(markerDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers must be the same dimension than the original image with a number of channels corresponding to the number of markers");
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
			for(int i = 0; i < numOfMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			numOfMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					markerColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				channelForMarker[i] = -1;
				thresholdForMarker[i][0] = -1;
				thresholdForMarker[i][1] = -1;
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
		currentMarker = -1;
		
		//Build GUI
		SwingUtilities.invokeLater(
				new Runnable() {
					public void run() {
						win = new CustomWindow(displayImage);
						win.pack();
					}
				});

		// refresh overlay
		IJ.wait(150);
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
		markerImage = null;
	}
	/**
	 * load marker identification
	 */
	private void loadMarkerIdentifications(ImagePlus markerImage) 
	{
		if (null == markerImage) return; // user canceled open dialog
		else {

			ImageStack stack = markerImage.getStack();
			int[] markerDims = markerImage.getDimensions();
			
			// test on nuclei segmentation image dimensions
			if ((markerDims[2]>1)&&(markerDims[3]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((markerDims[2]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((markerDims[3]>1)&&(markerDims[4]>1)) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers cannot have more than 3 dimensions: 1st and 2nd dimensions correspond to x and y, the 3rd dimension corresponds to the classe(s)");
				return;
			}
			if ((markerDims[0]!=displayImage.getWidth())||(markerDims[1]!=displayImage.getHeight())) {
				IJ.showMessage("Incompatible dimension", "The image with annotated nuclei markers must be the same dimension than the original image with a number of channels corresponding to the number of markers");
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
			for(int i = 0; i < numOfMarkers; i++) {
				for(int p=0;p<4;p++) {
					positiveNucleiForEachMarker[i][p] = null;
				}
				positiveNucleiForEachMarker[i] = null;
			}
			positiveNucleiForEachMarker = new ArrayList[MAX_NUM_MARKERS][4];
			numOfMarkers = 0;
			for(byte i = 0; i < MAX_NUM_MARKERS; i++) {
				for(byte p=0;p<4;p++) {
					markerColors[i][p] = (byte)(p+4);
				}
				markerCellcompartment[i] = 0;
				channelForMarker[i] = -1;
				thresholdForMarker[i][0] = -1;
				thresholdForMarker[i][1] = -1;
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
		currentMarker = -1;
		
		//Build GUI
		SwingUtilities.invokeLater(
				new Runnable() {
					public void run() {
						win = new CustomWindow(displayImage);
						win.pack();
					}
				});

		// refresh overlay
		IJ.wait(150);
		displayImage.setOverlay(markersOverlay);
		displayImage.updateAndDraw();
		markerImage = null;
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
		ImagePlus segmentednuclei = new ImagePlus("Segmented nuclei", stack);
		SaveDialog sd = new SaveDialog("Nuclei segmentation", "NucleiSegmentation", ".tif");
		final String dir = sd.getDirectory();
		final String filename = sd.getFileName();
		
		if(null == dir || null == filename)
			return;
		
		IJ.save(segmentednuclei, dir + filename);
	}
	
	/**
	 * save nuclear marker identifications
	 */
	private void saveNucleiIdentification() 
	{
		SaveDialog sd = new SaveDialog("Identified nuclei", "IdentifiedNuclei", ".tif");
		final String dir = sd.getDirectory();
		final String filename = sd.getFileName();

		if(null == dir || null == filename)
			return;

		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int maxOverlayId=0;
		for(int c=0;c<numOfMarkers;c++) {
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
		for(int c=0;c<numOfMarkers;c++) {
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
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), nucleiMarker));
		}
		ImagePlus segmentednuclei = new ImagePlus("Nuclei markers", stack);
		
		IJ.save(segmentednuclei, dir + filename);
	}
	private void saveNucleiIdentification(String outputFilename) 
	{
		ImageStack stack = new ImageStack(displayImage.getWidth(), displayImage.getHeight());
		int maxOverlayId=0;
		for(int c=0;c<numOfMarkers;c++) {
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
		for(int c=0;c<numOfMarkers;c++) {
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
			stack.addSlice(new FloatProcessor(displayImage.getWidth(), displayImage.getHeight(), nucleiMarker));
		}
		ImagePlus segmentednuclei = new ImagePlus("Nuclei markers", stack);
		
		IJ.save(segmentednuclei, outputFilename);
	}

	/**
	 * Repaint whole window
	 */
	private void repaintWindow() 
	{
		// Repaint window
		SwingUtilities.invokeLater(
				new Runnable() {
					public void run() {
						win.invalidate();
						win.validate();
						win.repaint();
					}
				});	
	}

}