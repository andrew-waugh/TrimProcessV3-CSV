package TrimProcessV3;

/**
 *
 * T R I M P R O C E S S V 3 C S V
 *
 * This class processes a CSV TRIM export and converts it into V3 VEOs.
 * <h3>Command Line arguments</h3>
 * The following command line arguments must be supplied:
 * <ul>
 * <li><b>-s &lt;PFXfile&gt; &lt;password&gt;</b> a PFX file containing details
 * about the signer (particularly the private key) and the password. The PFX
 * file can also be specified in the control file.
 * <li><b>[files|directories]+</b> a list of TRIM export files, or directories
 * containing such files.</li>
 * </ul>
 * <p>
 * The following command line arguments are optional:
 * <li><b>-v</b> verbose output. By default off.</li>
 * <li><b>-d</b> debug mode. In this mode more logging will be generated, and
 * the VEO directories will not be deleted after the ZIP file is created. By
 * default off.</li>
 * <li><b>-ha &lt;algorithm&gt;</b> The hash algorithm used to protect the
 * content files and create signatures. The default is 'SHA-512'.</li>
 * <li><b>-o &lt;outputDir&gt;</b> the directory in which the VEOs are to be
 * created. If not present, the VEOs will be created in the current
 * directory.</li>
 * <li><b>-t &lt;template&gt;</b> a file which contains AGLS metadata fields
 * (expressed as RDF) to be included in the root level metadata package of each
 * VEO created.</li>
 * <li><b>-r &lt;rdfid&gt;</b> a prefix used to construct the RDF identifiers.
 * If not present the string file:///[pathname] is used.</li>
 * </ul>
 * <p>
 * A minimal example of usage is<br>
 * <pre>
 *     trimprocessv3 -s text.pfx test TRIMExportFile.xml
 * </pre>
 *
 */
import java.util.TimeZone;
import java.util.Locale;
import java.util.Date;
import java.text.SimpleDateFormat;
import VEOCreate.CreateVEO;
import VEOCreate.Fragment;
import VERSCommon.AppError;
import VERSCommon.LTSF;
import VERSCommon.PFXUser;
import VERSCommon.VEOError;
import VERSCommon.VEOFatal;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;

public class TrimProcessV3CSV {

    static String classname = "TrimProcessV3-CSV"; // for reporting
    ArrayList<String> files;// files or directories to process
    static ByteArrayOutputStream baos = new ByteArrayOutputStream();
    Runtime r;
    long freemem;
    String missingXMLEntityExpln; // a description of why the XML entities were missing
    Path supportDir;        // directory in which is found the support information
    LTSF ltsf;              // valid long term sustainable formats
    boolean help;           // true if printing a cheat list of command line options

    // global variables storing information about this export (as a whole)
    Path sourceDirectory;   // directory in which TRIM objects are found
    Path contentDirectory;  // directory where content files are to be found (relative to source directory)
    Path outputDirectory;   // directory in which VEOS are to be generated
    Path templateDir;       // directory in which the template is to be found
    int exportCount;        // number of exports processed
    boolean incRevisions;   // include revisions of the final version
    boolean debug;          // true if in debug mode
    boolean verbose;        // true if in verbose output mode
    String rdfIdPrefix;     // prefix to be used to generate RDF identifiers
    String hashAlg;         // hash algorithm to use (default SHA-512)
    String userId;          // user performing the converstion
    PFXUser user;           // User that will sign the VEOs
    Fragment aglsCommon;    // template for common metadata elements
    SortedMap<String, TrimEntity> allEntities; // List of all entities found or referenced

    // global variables storing information extracted from a specific export.txt file
    String[] labels;        // list of column labels taken from the TRIM export file being processed
    int idCol;              // column in which to find the TRIM entity identifier
    int containerCol;       // column in which to find the container reference
    int containedCol;       // column in which to find the contained entities
    int titleCol;           // column in which the title is found
    int classificationCol;  // column in which the classification is found
    int dateCreatedCol;     // column in which the date the entity was created is found
    int dateRegisteredCol;  // column in which the date the entity was registered is found
    int recordTypeCol;      // column in which the record type is found
    int isPartCol;          // column in which the 'is part' info is found
    int docFileCol;         // column in which the attached file is to be found
    int retSchCol;          // column in which the retention schedule is to be found

    Path veoDirectory;    // directory representing the VEO
    Path dummyLTSFCF;       // file containing the dummyLTSF content file
    ArrayList<Embedded> revisions; // the revisions
    ArrayList<Embedded> renditions; // the renditions
    ArrayList<String> attachments; // attachments to emails
    ArrayList<String> staticChildren; // a static reference to the array list declared on the stack

    String revisionNo;      // identifier for this particular revision
    String renditionNo;     // identifier for this particular rendition

    // private final static Logger rootLog = Logger.getLogger("TrimProcessV3");
    private final static Logger LOG = Logger.getLogger("TrimProcessV3.TrimProcessV3CSV");

    /**
     * Report on version...
     *
     * <pre>
     * 20161114 1.1 Fixed bug with generating URI (dealing with odd characters in file name). Added command line arg to point to template directory.
     * 20210505 2.0 Updated & generalised to work with current Cabinet transfer
     * 20210709 2.1 Updated to work on PISA with BAT file
     * 20210712 2.2 Improved reporting
     * 20210714 2.3 Added content directory etc
     * </pre>
     */
    static String version() {
        return ("2.3");
    }

    /**
     * Default constructor
     *
     * @param args arguments passed to program
     * @throws VEOFatal if a fatal error occurred
     */
    public TrimProcessV3CSV(String args[]) throws VEOFatal {
        super();

        SimpleDateFormat sdf;
        TimeZone tz;

        // Set up logging
        // System.setProperty("java.util.logging.SimpleFormatter.format", "%4$s: %5$s%n"); with type of Log message
        System.setProperty("java.util.logging.SimpleFormatter.format", "%5$s%n");
        LOG.addHandler(new ConsoleHandler());
        LOG.setLevel(Level.WARNING);
        LOG.setUseParentHandlers(false);
        // rootLog.setLevel(Level.WARNING);

        // set up default global variables
        files = new ArrayList<>();
        sourceDirectory = Paths.get(".");
        contentDirectory = Paths.get(".");
        outputDirectory = Paths.get(".");
        templateDir = Paths.get(".");
        supportDir = null;
        missingXMLEntityExpln = "This portion of the record was not included as the XML representation was missing";
        debug = false;
        verbose = false;
        hashAlg = "SHA-512";
        rdfIdPrefix = null;
        userId = System.getProperty("user.name");
        if (userId == null) {
            userId = "Unknown user";
        }
        user = null;
        incRevisions = false;
        exportCount = 0;
        allEntities = new TreeMap<>();
        help = false;
        r = Runtime.getRuntime();

        // variables for processing this XML document
        labels = null;

        // process command line arguments
        configure(args);

        // tell what is happening
        LOG.log(Level.SEVERE, "******************************************************************************");
        LOG.log(Level.SEVERE, "*                                                                            *");
        LOG.log(Level.SEVERE, "*     T R I M   C V S   E X P O R T ( V 3 )   C R E A T I O N   T O O L      *");
        LOG.log(Level.SEVERE, "*                                                                            *");
        LOG.log(Level.SEVERE, "*                                Version " + version() + "                                *");
        LOG.log(Level.SEVERE, "*            Copyright 2015, 2021 Public Record Office Victoria              *");
        LOG.log(Level.SEVERE, "*                                                                            *");
        LOG.log(Level.SEVERE, "******************************************************************************");
        LOG.log(Level.SEVERE, "");
        tz = TimeZone.getTimeZone("GMT+10:00");
        sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss+10:00");
        sdf.setTimeZone(tz);
        LOG.log(Level.SEVERE, "Run at {0}", new Object[]{sdf.format(new Date())});
        LOG.log(Level.SEVERE, "");
        if (help) {
            // trimProcessV3 -t <directory> -s <pfxFile> <password> -support <directory> [-v] [-d] [-h hashAlg] [-o <directory>] [-a dir]* [-rev] files)*
            LOG.log(Level.SEVERE, "Command line arguments:");
            LOG.log(Level.SEVERE, " Mandatory:");
            LOG.log(Level.SEVERE, "  -s <pfxFile> <password>: path to a PFX file and its password for signing a VEO");
            LOG.log(Level.SEVERE, "  -t <directory>: file path to where the templates are located");
            LOG.log(Level.SEVERE, "  -suppport <directory>: path to a directory containing V3 support files (the LTSF definition)");
            LOG.log(Level.SEVERE, "  files: TRIM CSV/content export(s) files in the source directory");
            LOG.log(Level.SEVERE, "");
            LOG.log(Level.SEVERE, " Optional:");
            LOG.log(Level.SEVERE, "  -source <directory>: path to a directory containing the export (default is current working directory");
            LOG.log(Level.SEVERE, "  -content <directory>: path to a directory containing the content files (relative to source directory; default is current working directory");
            LOG.log(Level.SEVERE, "  -o <directory>: the directory in which the VEOs are created (default is current working directory)");
            LOG.log(Level.SEVERE, "  -h <hashAlgorithm>: specifies the hash algorithm (default SHA-256)");
            LOG.log(Level.SEVERE, "  -rev: include all revisions of the content (if present)");
            LOG.log(Level.SEVERE, "");
            LOG.log(Level.SEVERE, "  -v: verbose mode: give more details about processing");
            LOG.log(Level.SEVERE, "  -d: debug mode: give a lot of details about processing");
            LOG.log(Level.SEVERE, "  -help: print this listing");
            LOG.log(Level.SEVERE, "");
        }

        // check to see if at least one file or directory is specified
        if (files.isEmpty()) {
            throw new VEOFatal("You must specify at least one file or directory to process");
        }
        if (user == null) {
            throw new VEOFatal("You must specify a PFX file using the -s command line argument");
        }
        if (sourceDirectory == null) {
            throw new VEOFatal("You must specify a source directory using the -source command line argument");
        }
        if (contentDirectory == null) {
            throw new VEOFatal("You must specify a content directory using the -content command line argument");
        }
        contentDirectory = sourceDirectory.resolve(contentDirectory);
        if (supportDir == null) {
            throw new VEOFatal("You must specify a VERS support directory using the -suppoort command line argument");
        }
        if (templateDir == null) {
            throw new VEOFatal("You must specify a template directory using the -t command line argument");
        }

        // LOG generic things
        LOG.log(Level.SEVERE, "Source directory is ''{0}''", new Object[]{sourceDirectory.toAbsolutePath().toString()});
        LOG.log(Level.SEVERE, "Content directory is ''{0}''", new Object[]{contentDirectory.toAbsolutePath().toString()});
        LOG.log(Level.SEVERE, "Output directory is ''{0}''", new Object[]{outputDirectory.toAbsolutePath().toString()});
        LOG.log(Level.SEVERE, "Common AGLS metadata & VEOReadme.txt from ''{0}''", new Object[]{templateDir.toAbsolutePath().toString()});
        LOG.log(Level.SEVERE, "Support directory is ''{0}''", new Object[]{supportDir.toAbsolutePath().toString()});
        LOG.log(Level.SEVERE, "User id to be logged: ''{0}''", new Object[]{userId});
        LOG.log(Level.SEVERE, "PFX user is ''{0}''", new Object[]{user.getUserId()});
        LOG.log(Level.SEVERE, "Hash algorithm is ''{0}''", hashAlg);
        LOG.log(Level.SEVERE, "RDF Identifier prefix is ''{0}''", rdfIdPrefix);
        LOG.log(Level.SEVERE, "Verbose output selected: {0}", new Object[]{verbose});
        LOG.log(Level.SEVERE, "Debug mode selected: {0}", new Object[]{debug});
        if (incRevisions) {
            LOG.log(Level.SEVERE, "Including revisions");
        }
        LOG.log(Level.SEVERE, "");

        // get template for AGLS metadata
        aglsCommon = Fragment.parseTemplate(templateDir.resolve("aglsCommon.txt").toFile());
        ltsf = new LTSF(supportDir.resolve("validLTSF.txt"));

        try {
            missingXMLEntityExpln = getExplanation(templateDir.resolve("missingXMLEntityExpln.txt"));
        } catch (VEOError ve) {
            /* ignore */
        }
    }

    /**
     * Configure
     *
     * This method gets the options for this run of the manifest generator from
     * the command line. See the comment at the start of this file for the
     * command line arguments.
     *
     * @param args[] the command line arguments
     * @param VEOFatal if a fatal error occurred
     */
    private void configure(String args[]) throws VEOFatal {
        int i;
        Path pfxFile;           // PFX file to use for signing. If null, don't sign
        String pfxFilePassword; // Password to unlock PFX file
        String usage = "trimProcessV3 [-help] -t <directory> -s <pfxFile> <password> -support <directory> [-v] [-d] [-ha hashAlg] [-o <directory>] [-a dir]* [-rev] [-source <directory>] [-content <directory>] (files)*";

        // process command line arguments
        i = 0;
        try {
            while (i < args.length) {
                switch (args[i]) {

                    // verbose?
                    case "-v":
                        verbose = true;
                        LOG.setLevel(Level.INFO);
                        i++;
                        break;

                    // debug?
                    case "-d":
                        debug = true;
                        LOG.setLevel(Level.FINE);
                        i++;
                        break;

                    // display help?
                    case "-help":
                        help = true;
                        i++;
                        break;

                    // get pfx file
                    case "-s":
                        i++;
                        pfxFile = checkFile("PFX file", args[i], false);
                        i++;
                        pfxFilePassword = args[i];
                        i++;
                        user = new PFXUser(pfxFile.toString(), pfxFilePassword);
                        break;

                    // get hash algorithm
                    case "-ha":
                        i++;
                        hashAlg = args[i];
                        i++;
                        break;

                    // '-o' specifies where VEOs are created
                    case "-o":
                        i++;
                        outputDirectory = checkFile("output directory", args[i], true);
                        i++;
                        break;

                    // '-source' specifies directory where data is found
                    case "-source":
                        i++;
                        sourceDirectory = checkFile("source directory", args[i], true);
                        i++;
                        break;

                    // '-content' specifies directory where data is found relative to source directory
                    case "-content":
                        i++;
                        contentDirectory = checkFile("content directory", args[i], true);
                        i++;
                        break;

                    // '-support' specifies support directory (where the LTSF is defined)
                    case "-support":
                        i++;
                        supportDir = checkFile("support directory", args[i], true);
                        i++;
                        break;

                    // '-t' specifies a file that contains invarient metadata for AGLS metadata package
                    case "-t":
                        i++;
                        templateDir = checkFile("common AGLS metadata template", args[i], true);
                        i++;
                        break;

                    // '-r' specifies the RDF prefix (i.e. http://blah//)
                    case "-r":
                        i++;
                        rdfIdPrefix = args[i];
                        i++;
                        break;

                    // '-rev' means include all the revisions
                    case "-rev":
                        i++;
                        incRevisions = true;
                        break;

                    default:
                        // if unrecognised arguement, print help string and exit
                        if (args[i].charAt(0) == '-') {
                            throw new VEOFatal("Unrecognised argument '" + args[i] + "' Usage: " + usage);
                        }

                        // if doesn't start with '-' assume a file
                        files.add(args[i]);
                        i++;
                        break;
                }
            }
        } catch (ArrayIndexOutOfBoundsException ae) {
            throw new VEOFatal("Missing argument. Usage: " + usage);
        } catch (VEOFatal vf) {
            throw new VEOFatal("Fatal error: " + vf.toString());
        }
    }

    /**
     * Check a file to see that it exists and is of the correct type (regular
     * file or directory). The program terminates if an error is encountered.
     *
     * @param type a String describing the file to be opened
     * @param name the file name to be opened
     * @param isDirectory true if the file is supposed to be a directory
     * @throws VEOFatal if the file does not exist, or is of the correct type
     * @return the File opened
     */
    private Path checkFile(String type, String name, boolean isDirectory) throws VEOFatal {
        Path p;

        p = Paths.get(name);

        if (!Files.exists(p)) {
            throw new VEOFatal(classname, 6, type + " '" + p.toAbsolutePath().toString() + "' does not exist");
        }
        if (isDirectory && !Files.isDirectory(p)) {
            throw new VEOFatal(classname, 7, type + " '" + p.toAbsolutePath().toString() + "' is a file not a directory");
        }
        if (!isDirectory && Files.isDirectory(p)) {
            throw new VEOFatal(classname, 8, type + " '" + p.toAbsolutePath().toString() + "' is a directory not a file");
        }
        return p;
    }

    /**
     * getExplanation
     *
     * This reads an explanation of a problem from a file in the template
     * directory.
     */
    private String getExplanation(Path labels) throws VEOError {
        FileReader fr = null;
        BufferedReader br = null;
        String line;
        StringBuffer sb;

        sb = new StringBuffer();
        try {
            fr = new FileReader(labels.toString());
            br = new BufferedReader(fr);
            while ((line = br.readLine()) != null) {
                sb.append(line);
                sb.append("\n");
            }
        } catch (FileNotFoundException fnfe) {
            LOG.log(Level.WARNING, "Explanation file ''{0}'' does not exist", new Object[]{labels.toString()});
            throw new VEOError(fnfe.getMessage());
        } catch (IOException ioe) {
            LOG.log(Level.WARNING, "Error when reading Explanation file ''{0}'': ''{1}''", new Object[]{labels.toString(), ioe.getMessage()});
            throw new VEOError(ioe.getMessage());
        } finally {
            try {
                if (br != null) {
                    br.close();
                }
            } catch (IOException e) {
                /* ignore */
            }
            try {
                if (fr != null) {
                    fr.close();
                }
            } catch (IOException e) {
                /* ignore */
            }
        }
        return sb.toString();
    }

    /**
     * processExports
     *
     * This method processes the list of files or exports
     * @throws VERSCommon.VEOFatal
     */
    public void processExports() throws VEOFatal {
        int i;
        String file;

        // go through the list of files
        freemem = r.freeMemory();
        for (i = 0; i < files.size(); i++) {
            file = files.get(i);
            if (file == null) {
                continue;
            }
            processTRIMEntityFile(sourceDirectory.resolve(file));
        }
    }

    /**
     * ProcessTRIMEntityFile
     *
     * Read the TRIM entity file and extract the details for building the VEOs
     */
    private void processTRIMEntityFile(Path f) throws VEOFatal {
        SortedMap<String, TrimEntity> entities; // record of entities found or referenced

        // check that file or directory exists
        LOG.log(Level.INFO, "Extracting TRIM entities from ''{0}''", new Object[]{f.toAbsolutePath().toString()});
        if (!Files.exists(f)) {
            LOG.log(Level.WARNING, "***File ''{0}'' does not exist", new Object[]{f.toString()});
            return;
        }

        // convert the TRIM entity file into a set of TRIM entities & process them
        try {
            LOG.log(Level.INFO, "Reading TRIM entities");
            entities = readTrimEntityFile(f);
            if (entities != null) {
                LOG.log(Level.INFO, "Processing the TRIM entities");
                processTrimEntities(entities);
            } else {
                LOG.log(Level.INFO, "No TRIM entities found to be processed");
            }
            rememberTrimEntities(entities, f.getParent());
        } catch (VEOError e) {
            throw new VEOFatal("***Failed to read TRIM entity file '" + f.toAbsolutePath().toString() + "' because: " + e.getMessage());
        }
    }

    /**
     * Read the TRIM entity file. The entity file contains details about the
     * TRIM entities produced during this export. This is a text table with each
     * line consisting of multiple strings separated by tabs. The first line
     * contains the titles of the columns (i.e. metadata labels). Each
     * subsequent line contains one TRIM entity
     *
     * @param f the path of the TRIM entity file
     * @return a sorted map of TRIM entities in the file
     * @throws VEOError if an error occurred, but processing can continue with
     * other files
     */
    private SortedMap<String, TrimEntity> readTrimEntityFile(Path f) throws VEOFatal {
        Path dir;
        FileReader fr = null;
        BufferedReader br = null;
        String line, key;
        String[] tokens;
        int i;
        int lineNo;
        TrimEntity te;
        SortedMap<String, TrimEntity> entities; // record of entities found or referenced

        // get the directory that contains this TRIM entity file
        dir = f.getParent();
        if (dir == null) {
            throw new VEOFatal("Failed because could not open parent directory");
        }
        entities = new TreeMap<>();
        try {
            FileInputStream fs = new FileInputStream(f.toFile());
            InputStreamReader isr = new InputStreamReader(fs, StandardCharsets.UTF_16);
            br = new BufferedReader(isr);
            idCol = -1;
            containerCol = -1;
            containedCol = -1;
            titleCol = -1;
            dateCreatedCol = -1;
            recordTypeCol = -1;
            isPartCol = -1;
            docFileCol = -1;
            retSchCol = -1;
            lineNo = 1;
            while ((line = br.readLine()) != null) {

                // read a line and split it at tabs
                //line = line.trim();
                if (line.isEmpty()) {
                    continue;
                }
                tokens = line.split("\t");

                // assume that the first row has the column headings. This
                // remembers the column number of metadata elements that will
                // be later pulled out.
                if (lineNo == 1) {
                    LOG.log(Level.FINE, "Columns in source TSV file:  {0}", new Object[]{tokens.length});
                    for (i = 0; i < tokens.length; i++) {
                        switch (tokens[i].trim()) {
                            case "Expanded Number":
                                idCol = i;
                                break;
                            case "Folder":
                            case "Container":
                                containerCol = i;
                                break;
                            case "*Contained Records*":
                                containedCol = i;
                                break;
                            case "Title (Free Text Part)":
                                titleCol = i;
                                break;
                            case "Classification":
                                classificationCol = i;
                                break;
                            case "Date Created":
                                dateCreatedCol = i;
                                break;
                            case "Date Registered":
                                dateRegisteredCol = i;
                                break;
                            case "Record Type":
                                recordTypeCol = i;
                                break;
                            case "*Is Part*":
                                isPartCol = i;
                                break;
                            case "DOS file":
                                docFileCol = i;
                                break;
                            case "Retention schedule":
                                retSchCol = i;
                                break;
                            default:
                                break;
                        }
                    }
                    if (idCol == -1) {
                        throw new VEOFatal("Could not find 'Expanded Number' column");
                    }
                    if (containerCol == -1) {
                        throw new VEOFatal("Could not find 'Container' column");
                    }
                    /*
                    if (containedCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find '*Contained Records*' column");
                    }
                     */
                    if (titleCol == -1) {
                        throw new VEOFatal("Could not find 'Title (Free Text Part)' column");
                    }
                    if (classificationCol == -1) {
                        throw new VEOFatal("Could not find 'Classification' column");
                    }
                    if (dateCreatedCol == -1) {
                        throw new VEOFatal("Could not find 'Date Created' column");
                    }
                    if (dateRegisteredCol == -1) {
                        throw new VEOFatal("Could not find 'Date Registered' column");
                    }
                    if (recordTypeCol == -1) {
                        throw new VEOFatal("Could not find 'Record Type' column");
                    }
                    /*
                    if (isPartCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find '*Is Part*' column");
                    }
                     */
                    if (docFileCol == -1) {
                        throw new VEOFatal("Could not find 'DOS File' column");
                    }
                    if (retSchCol == -1) {
                        throw new VEOFatal("Could not find 'Retention schedule' column");
                    }
                    labels = tokens;
                } else if (lineNo > 1) {
                    // create a TrimEntity of this row
                    key = tokens[idCol].trim();
                    te = entities.get(key);
                    if (te == null) {
                        te = new TrimEntity(key, tokens, dir);
                        entities.put(key, te);
                    }
                    te.defined = true;

                    te.veoName = tokens[idCol];
                    if (tokens[containerCol] != null && !tokens[containerCol].equals("")) {
                        te.container = new TrimID(tokens[containerCol]);
                    }
                    te.title = tokens[titleCol];
                    te.dateCreated = tokens[dateCreatedCol];
                    te.contentFile = tokens[docFileCol];
                    te.dateRegistered = tokens[dateRegisteredCol];
                    te.classification = tokens[classificationCol];
                    switch (tokens[recordTypeCol]) {
                        case "CABINET FILE":
                            te.recordType = "Cabinet File";
                            break;
                        case "CABINET DOCUMENT":
                            te.recordType = "Cabinet Document";
                            break;
                        case "CORPORATE DOCUMENT":
                            te.recordType = "Corporate Document";
                            break;
                        case "DOCUMENT GROUP":
                            te.recordType = "Document Group";
                            break;
                        case "EBC DOCUMENT":
                            te.recordType = "EBC Document";
                            break;
                        case "EBC FOLDER":
                            te.recordType = "EBC Folder";
                            break;
                        case "MINISTERIAL BRIEFING - VERS":
                            te.recordType = "Ministerial Briefing - VERS";
                            break;
                        case "MINISTERIAL BRIEFING":
                            te.recordType = "Ministerial Briefing";
                            break;
                        case "MINISTERIAL CORRESPONDENCE  - VERS":
                            te.recordType = "Ministerial Correspondence - VERS";
                            break;
                        default:
                            LOG.log(Level.WARNING, "Unhandled record type: ''{0}'' in ''{1}''", new Object[]{tokens[recordTypeCol], f.toAbsolutePath().toString()});
                            te.recordType = tokens[recordTypeCol];
                            break;
                    }
                    te.retentionSchedule = tokens[retSchCol];
                    LOG.log(Level.INFO, "Metadata extracted from line({0}): ''{1}''", new Object[]{lineNo, te.toString()});
                }
                lineNo++;
            }
        } catch (FileNotFoundException fnfe) {
            throw new VEOFatal("File does not exist");
        } catch (IOException ioe) {
            throw new VEOFatal("Error when reading TRIM entity file: " + ioe.getMessage());
        } finally {
            try {
                if (br != null) {
                    br.close();
                }
            } catch (IOException e) {
                /* ignore */
            }
            try {
                if (fr != null) {
                    fr.close();
                }
            } catch (IOException e) {
                /* ignore */
            }
        }
        return entities;
    }

    /**
     * Remember the TRIM entities for the reporting at the end of the run.
     */
    private void rememberTrimEntities(SortedMap<String, TrimEntity> entities, Path dir) throws VEOError {
        Iterator<String> it;
        String key, refID;
        TrimEntity te, te1;
        int i;

        // go through TRIM entities
        it = entities.keySet().iterator();
        while (it.hasNext()) {
            key = it.next();
            te = entities.get(key);

            // if this contains other entities, mark the others as referenced
            if (te.refs != null) {
                for (i = 0; i < te.refs.size(); i++) {
                    refID = te.refs.get(i);
                    te1 = entities.get(refID);
                    if (te1 == null) {
                        te1 = new TrimEntity(key, null, dir);
                        allEntities.put(key, te1);
                    }
                    te1.referenced = true;
                    te1.referencedBy.append(key + ", ");
                }
            }

            // add to complete list of entities seen
            allEntities.put(key, te);
        }
    }

    /**
     * Process the TRIM entities This function goes through list of TRIM
     * entities read from the TRIM export file and selects the root entities to
     * construct VEOs from
     */
    private void processTrimEntities(SortedMap<String, TrimEntity> entities) {
        Iterator<String> it;
        String key;
        TrimEntity te;

        // go through TRIM entities
        it = entities.keySet().iterator();
        while (it.hasNext()) {
            key = it.next();
            te = entities.get(key);

            // process the entity if it is a root entity
            if (te.tokens[containerCol] == null || te.tokens[containerCol].equals("")) {
                te.root = true;
                try {
                    createVEO(te, entities);
                } catch (VEOError | AppError e) {
                    LOG.log(Level.SEVERE, "Failed to build VEO ''{0}'' because {1}", new Object[]{key, e.getMessage()});
                }
            }
        }
    }

    /**
     * Create VEO
     *
     * This method creates a new VEO
     *
     * @param xmlFile	the file to parse
     * @throws VEOError if an error occurred that prevented the processing of
     * this XML file
     */
    private void createVEO(TrimEntity base, SortedMap<String, TrimEntity> entities) throws VEOError, AppError {
        long l;
        CreateVEO cv;
        Path p;
        String recordName;      // name of this record element (the id of the root TRIM entity)
        String description[] = {"Created with TrimProcessV3"};
        String errors[] = {""};
        SimpleDateFormat sdf = new SimpleDateFormat("HH:mm:ss");

        // check parameters
        if (base == null) {
            throw new VEOFatal("createVEO: Passed null base to be processed");
        }
        if (entities == null) {
            throw new VEOFatal("createVEO: Passed null list of entities to be processed");
        }

        // reset, free memory, and print status
        baos.reset();
        r.gc();
        l = r.freeMemory();
        LOG.log(Level.INFO, "{0} Processing: {1}", new Object[]{sdf.format(new Date()), base.name});
        freemem = l;
        dummyLTSFCF = null;

        // get the record name from the root TRIM entity
        recordName = base.id.toString().replace('/', '-');

        // create a record directory in the output directory
        p = Paths.get(outputDirectory.toString(), recordName + ".veo");
        if (!deleteDirectory(p)) {
            throw new VEOError("Arrgh: directory '" + p.toString() + "' already exists & couldn't be deleted");
        }
        try {
            veoDirectory = Files.createDirectory(p);
        } catch (IOException ioe) {
            throw new VEOError("Arrgh: could not create record directory '" + p.toString() + "': " + ioe.toString());
        }

        // create VEO...
        cv = new CreateVEO(outputDirectory, recordName, hashAlg, verbose);
        try {
            cv.addVEOReadme(supportDir);
            cv.addEvent(versDateTime(System.currentTimeMillis()), "Converted to VEO", userId, description, errors);
            processTrimEntity(base, entities, cv, recordName, 1, recordName + ".veo.zip");
            cv.finishFiles();
            cv.sign(user, hashAlg);
            cv.finalise(true);
            base.exported = true;
        } catch (VEOError ve) {
            cv.abandon(true);
            throw new VEOError(ve.getMessage());
        } finally {
            System.gc();
        }

        // count the number of exports successfully processed
        exportCount++;
    }

    /**
     * Process TRIM entity
     *
     * @param cv the VEO being created
     * @param xmlFile	the file to parse
     * @param recordName the name of the Information Object to be produced
     * @param depth the depth of the Information Object
     * @param veoName the name of the VEO being produced
     * @throws VEOError if an error occurred that prevented the processing of
     * this XML file
     */
    private void processTrimEntity(TrimEntity base, SortedMap<String, TrimEntity> entities, CreateVEO cv, String recordName, int depth, String veoName) throws VEOError, AppError {
        int i;
        String label;
        String[] data = {};
        ArrayList<String> children;
        URI uri;
        String s;
        Iterator<String> teKeys;
        String[] contents;
        TrimEntity t;
        Path p;

        // set up
        revisions = new ArrayList<>();
        renditions = new ArrayList<>();
        attachments = new ArrayList<>();
        children = new ArrayList<>();

        staticChildren = null;

        // add the information object
        try {
            // make a label for the information object, comprised of a TRIM record type and the record id
            s = base.tokens[recordTypeCol];
            if (s == null || s.equals("")) {
                label = null;
                // label = recordName;
            } else {
                label = "Cabinet-in-Confidence Departmental Working Records: " + base.recordType;
            }

            // create information object
            cv.addInformationObject(label, depth);

            // add the AGLS metadata package
            cv.addMetadataPackage("http://prov.vic.gov.au/vers/schema/AGLS", "http://www.w3.org/1999/02/22-rdf-syntax-ns", null);
            cv.continueMetadataPackage(" <rdf:RDF xmlns:dcterms=\"http://purl.org/dc/terms/\"\n");
            cv.continueMetadataPackage("\txmlns:aglsterms=\"http://www.agls.gov.au/agls/terms/\"\n");
            cv.continueMetadataPackage("\txmlns:versterms=\"http://www.prov.vic.gov.au/vers/terms/\">\n");
            cv.continueMetadataPackage(" <rdf:Description rdf:about=\"");
            try {
                if (rdfIdPrefix == null) {
                    uri = new URI("file", null, "/" + recordName, null);
                } else {
                    uri = new URI(rdfIdPrefix, null, "/" + recordName, null);
                }
                cv.continueMetadataPackage(uri.toASCIIString());
            } catch (URISyntaxException use) {
                throw new VEOError("Failed building URI when generating RDF: " + use.toString());
            }
            cv.continueMetadataPackage("\">\n");
            cv.continueMetadataPackage(makeAGLSmetadata(base));
            if (aglsCommon != null) {
                cv.continueMetadataPackage(aglsCommon, data);
            }
            cv.continueMetadataPackage(" </rdf:Description>\n</rdf:RDF>\n");

            // add metadata package containing TRIM metadata
            cv.addMetadataPackage("http://prov.vic.gov.au/vers/schema/TRIM", "https://www.w3.org/TR/2008/REC-xml-20081126/", makeTrimMetadata(base));

            // add final version of record and any encodings (renditions in TRIM speak)
            if (base.contentFile != null && !base.contentFile.equals("")) {

                // get the content files for this TRIM entity. There will be two
                // file names, separated by a '|'. The first is the internal TRIM
                // file name, the second appears to be the original file name.
                // We use the second one...
                contents = base.contentFile.replace('|', '\t').split("\t");
                if (contents.length == 2) {
                    i = 1;
                } else {
                    i = 0;
                }

                // add an information piece with a single content file
                String veoRef = (recordName.replace('/', '-') + "/" + contents[i]);
                p = contentDirectory.resolve(contents[i]);
                try {
                    cv.addInformationPiece(null);
                    cv.addContentFile(veoRef, p);
                } catch (VEOError e) {
                    throw new VEOError("Information Object " + base.name + " is incomplete because: " + e.getMessage());
                }

                // if the content file wasn't a valid long term preservation
                // format, add a dummy content file with a .txt content
                if (!isLTPF(contents[i])) {
                    LOG.log(Level.WARNING, "File ''{0}'' has no long term sustainable format", new Object[]{p.toString()});
                    if (dummyLTSFCF == null) {
                        p = sourceDirectory.resolve("DummyContentFile.txt");
                        try {
                            try (FileWriter fw = new FileWriter(p.toAbsolutePath().toString()); BufferedWriter bw = new BufferedWriter(fw)) {
                                bw.write("This Information Piece has no content in an approved long term preservation format\n");
                            }
                            dummyLTSFCF = p;
                        } catch (IOException ioe) {
                            throw new VEOError("Failed attempting to add DummyContentFile: " + ioe.getMessage());
                        }
                    }
                    veoRef = (recordName.replace('/', '-') + "/DummyContentFile.txt");
                    cv.addContentFile(veoRef, dummyLTSFCF);
                }
            }

            // find contained entities. All contained entities are assumed to be
            // in the one source directory (hence are in the TRIM entity list)
            // Contained entries are found by looking for entities that have a
            // container metadata that matches the current base. This is because
            // the contained records element is complex
            TrimID ti = base.id;
            teKeys = entities.keySet().iterator();
            while (teKeys.hasNext()) {
                s = teKeys.next();
                t = entities.get(s);
                if (t.container != null && t.container.equals(ti)) {
                    processTrimEntity(t, entities, cv, t.tokens[idCol].trim(), depth + 1, veoName);
                }
            }
        } catch (VEOError ve) {
            cv.abandon(true);
            throw ve;
        } finally {
            // free everything about processing that XML document
            if (revisions != null) {
                for (i = 0; i < revisions.size(); i++) {
                    revisions.get(i).free();
                }
                revisions = null;
            }
            if (renditions != null) {
                for (i = 0; i < renditions.size(); i++) {
                    renditions.get(i).free();
                }
                renditions = null;
            }
            children.clear();
            if (attachments != null) {
                attachments.clear();
                attachments = null;
            }
        }
    }

    /**
     * Test to see if file is a LTPF The file extension is extracted from the
     * filename and looked up in the array of valid LTPFs
     */
    private boolean isLTPF(String filename) {
        String filetype;
        int i;

        if ((i = filename.lastIndexOf('.')) == -1) {
            return false;
        }
        filetype = filename.substring(i).toLowerCase();
        return ltsf.isV3LTSF(filetype);
    }

    /**
     * Add dummy information object when the real TRIM XML entity cannot be read
     * - either it doesn't exist, or the XML parsing failed.
     *
     * @param cv the VEO containing the invalid XML entity
     * @param recordName the TRIM name of the XML entity (obtained from the file
     * name)
     * @param depth the depth of the entity in the tree
     * @param description a description of the error
     */
    private void addDummyInfoObj(CreateVEO cv, String recordName, int depth, String description) throws VEOError {
        URI uri;

        cv.addInformationObject(recordName, depth);

        // add the AGLS metadata package
        cv.addMetadataPackage("http://prov.vic.gov.au/vers/schema/AGLS", "http://www.w3.org/1999/02/22-rdf-syntax-ns", null);
        cv.continueMetadataPackage(" <rdf:RDF xmlns:dcterms=\"http://purl.org/dc/terms/\"\n");
        cv.continueMetadataPackage("\txmlns:aglsterms=\"http://www.agls.gov.au/agls/terms/\"\n");
        cv.continueMetadataPackage("\txmlns:versterms=\"http://www.prov.vic.gov.au/vers/terms/\">\n");
        cv.continueMetadataPackage(" <rdf:Description rdf:about=\"");
        try {
            if (rdfIdPrefix == null) {
                uri = new URI("file", null, "/" + recordName, null);
            } else {
                uri = new URI(rdfIdPrefix, null, "/" + recordName, null);
            }
            cv.continueMetadataPackage(uri.toASCIIString());
        } catch (URISyntaxException use) {
            throw new VEOError("Failed building URI when generating RDF: " + use.toString());
        }
        cv.continueMetadataPackage("\">\n");
        cv.continueMetadataPackage(" <dcterms:title>");
        cv.continueMetadataPackage(XMLencode(recordName));
        cv.continueMetadataPackage("</dcterms:title>\n");
        cv.continueMetadataPackage(" <dcterms:created rdf:datatype=\"xsd:dateTime\">");
        cv.continueMetadataPackage(XMLencode(versDateTime(0)));
        cv.continueMetadataPackage("</dcterms:created>\n");
        cv.continueMetadataPackage(" <dcterms:description>");
        cv.continueMetadataPackage(XMLencode(description));
        cv.continueMetadataPackage("</dcterms:description>\n");
        cv.continueMetadataPackage(" <dcterms:identifier>");
        cv.continueMetadataPackage(XMLencode(recordName));
        cv.continueMetadataPackage("</dcterms:identifier>\n");
        cv.continueMetadataPackage(" </rdf:Description>\n</rdf:RDF>\n");
    }

    /**
     * Recursively delete a directory
     */
    private boolean deleteDirectory(Path directory) {
        DirectoryStream<Path> ds;
        boolean failed;

        failed = false;
        try {
            if (!Files.exists(directory)) {
                return true;
            }
            ds = Files.newDirectoryStream(directory);
            for (Path p : ds) {
                if (!Files.isDirectory(p)) {
                    try {
                        Files.delete(p);
                    } catch (IOException e) {
                        failed = true;
                    }
                } else {
                    failed |= !deleteDirectory(p);
                }
            }
            ds.close();
            if (!failed) {
                Files.delete(directory);
            }
        } catch (IOException e) {
            failed = true;
        }
        return !failed;
    }

    /**
     * Make the main (AGLS) metadata package
     *
     * @param e the TRIM entity to extract metadata from
     */
    private String makeAGLSmetadata(TrimEntity e) throws AppError {
        StringBuffer sb;

        sb = new StringBuffer();
        sb.append(" <dcterms:title>");
        sb.append(XMLencode(e.tokens[titleCol]));
        sb.append("</dcterms:title>\n");
        // case "trim/record/datecreated":
        sb.append(" <dcterms:created rdf:datatype=\"xsd:dateTime\">");
        sb.append(processDate(e.tokens[dateCreatedCol]));
        sb.append("</dcterms:created>\n");
        // case "trim/record/recordtype":
        sb.append(" <dcterms:type>");
        sb.append(XMLencode(e.tokens[recordTypeCol]));
        sb.append("</dcterms:type>\n");
        sb.append(" <dcterms:description>");
        sb.append(XMLencode(e.recordType));
        sb.append("</dcterms:description>\n");
        // case "trim/record/container":
        /*
        sb.append(" <dcterms:isPart>");
        sb.append(XMLencode(e.tokens[isPartCol]));
        sb.append("</dcterms:isPart>\n");
         */
 /*
        // case "trim/record/classification":
        currentEntity.classification = e.tokens[titleCol];
        // case "trim/record/dateregistered":
        currentEntity.dateRegistered = processDate(e.tokens[titleCol]);
         */
        // case "trim/record/longnumber":
        sb.append(" <dcterms:identifier>");
        sb.append(XMLencode(e.tokens[idCol]));
        sb.append("</dcterms:identifier>\n");
        return sb.toString();
    }

    /**
     * Make TRIM metadata This simply outputs the TRIM metadata into XML
     */
    private StringBuilder makeTrimMetadata(TrimEntity e) {
        StringBuilder sb, sb1;
        String s;
        int i, j;
        char c;

        sb = new StringBuilder();
        for (i = 0; i < labels.length; i++) {
            if (labels[i] == null || labels[i].equals("")) {
                continue;
            }
            // temporarily don't output empty elements
            if (i >= e.tokens.length || e.tokens[i] == null || e.tokens[i].equals("")) {
                continue;
            }

            // get rid of all non-alphanumeric characters in the label as
            // otherwise its not a valid XML element tag
            sb1 = new StringBuilder();
            for (j = 0; j < labels[i].length(); j++) {
                c = labels[i].charAt(j);
                if (Character.isLetterOrDigit(c)) {
                    sb1.append(c);
                }
            }
            s = sb1.toString();

            // output metadata as XML
            sb.append("   <");
            sb.append(s);
            if (i >= e.tokens.length || e.tokens[i] == null || e.tokens[i].equals("")) {
                sb.append("/>\n");
            } else {
                sb.append(">");
                sb.append(XMLencode(e.tokens[i]));
                sb.append("</");
                sb.append(s);
                sb.append(">\n");
            }
        }
        return sb;
    }

    /**
     * Function to process the TRIM date into an ISO8601 date. The TRIM date has
     * the format yyyymmddhhmmss. Some or all of the fine time divisions may not
     * be present
     *
     * @param date the TRIM date
     * @return the ISO8601 date
     */
    private String processDate(String date) throws AppError {
        String year, month, day, hour, min, sec;

        if (date == null || date.length() < 4) {
            throw new AppError("Failed converting date '" + date + "': date is null or less than 4 characters long");
        }
        year = date.substring(0, 4);
        if (date.length() == 4) {
            return year;
        }
        if (date.length() < 6) {
            throw new AppError("Failed converting date '" + date + "': date is less than 6 characters long");
        }
        month = date.substring(4, 6);
        if (date.length() == 6) {
            return year + "-" + month;
        }
        if (date.length() < 8) {
            throw new AppError("Failed converting date '" + date + "': date is less than 8 characters long");
        }
        day = date.substring(6, 8);
        if (date.length() == 8) {
            return year + "-" + month + "-" + day;
        }
        if (date.length() < 10) {
            throw new AppError("Failed converting date '" + date + "': date is less than 10 characters long");
        }
        hour = date.substring(8, 10);
        if (date.length() == 10) {
            return year + "-" + month + "-" + day + "T" + hour + ":00";
        }
        if (date.length() < 12) {
            throw new AppError("Failed converting date '" + date + "': date is less than 12 characters long");
        }
        min = date.substring(10, 12);
        if (date.length() == 12) {
            return year + "-" + month + "-" + day + "T" + hour + ":" + min;
        }
        if (date.length() < 14) {
            throw new AppError("Failed converting date '" + date + "': date is less than 14 characters long");
        }
        sec = date.substring(12, 14);
        return year + "-" + month + "-" + day + "T" + hour + ":" + min + ":" + sec;

    }

    /**
     * Private class to represent an embedded document
     */
    private class Embedded {

        String filename;    // name of embedded file
        String file;        // name of file in VEO content directory
        String extension;   // file extension
        StringBuilder value;

        public Embedded(String filename, String extension, String file, StringBuilder value) {
            this.filename = filename;
            this.extension = extension;
            this.file = file;
            this.value = value;
        }

        public void free() {
            filename = null;
            extension = null;
            if (value != null) {
                value.setLength(0);
            }
            value = null;
        }
    }

    /**
     * Report
     *
     * Report on any TRIM entities in the directory that were either referenced
     * as children, but did not exist, or existed but were not referenced as
     * children
     */
    public void report() {
        Iterator<String> it;
        boolean anyFound;
        TrimEntity te;

        // Ouput report
        LOG.log(Level.SEVERE, "");
        LOG.log(Level.SEVERE, "RESULT OF PROCESSING TRIM EXPORT");
        LOG.log(Level.SEVERE, "Total records (VEOs) created: {0}", new Object[]{exportCount});
        LOG.log(Level.SEVERE, "");

        // Report on root entities
        it = allEntities.keySet().iterator();
        anyFound = false;
        LOG.log(Level.INFO, "VEOs generated:");
        while (it.hasNext()) {
            te = allEntities.get(it.next());
            if (te.exported) {
                LOG.log(Level.INFO, "\t{0} in {1}", new Object[]{te.id, te.dir.toString()});
                // System.out.println("\t" + te.id + " " + te.dateCreated + " (" + te.title + ")");
                anyFound = true;
            }
        }
        if (!anyFound) {
            LOG.log(Level.INFO, "\tNo VEOs were generated");
        }

        // Reports on all entities exported
        produceCVS("ExportedReport.txt", true, false);
        // Reports on all entities found
        produceCVS("AllEntities.txt", false, false);
        // Reports on all root entities exported
        produceCVS("AllFiles.txt", true, true);
    }

    /*
     * Produce a CVS report about the TRIM entities processed
     * @param filename the report to generate (in the output directory)
     * @param onlyExported true if only report on exported TRIM entities
     * @param onlyRoot true if only report on exported root TRIM entities
     */
    private void produceCVS(String filename, boolean onlyExported, boolean onlyRoot) {
        Iterator<String> it;
        FileWriter fw;
        BufferedWriter bw;
        Path rep;
        TrimEntity te;

        rep = Paths.get(outputDirectory.toString(), filename);
        try {
            fw = new FileWriter(rep.toFile());
            bw = new BufferedWriter(fw);

            bw.write("ID\tVEO Name\tContainer\tTitle\tDate Created\tDate Registered\tClassification\tRecord Type\r\n");
            it = allEntities.keySet().iterator();
            while (it.hasNext()) {
                te = allEntities.get(it.next());
                if (onlyExported && !te.exported) {
                    continue;
                }
                if (onlyExported && onlyRoot && !te.root) {
                    continue;
                }
                bw.write(te.id.toString());
                bw.write("\t");
                if (te.veoName != null) {
                    bw.write(te.veoName);
                }
                bw.write("\t");
                if (te.container != null) {
                    bw.write(te.container.toString());
                }
                bw.write("\t");
                if (te.title != null) {
                    bw.write(te.title);
                }
                bw.write("\t");
                if (te.dateCreated != null) {
                    bw.write(te.dateCreated);
                }
                bw.write("\t");
                if (te.dateRegistered != null) {
                    bw.write(te.dateRegistered);
                }
                bw.write("\t");
                if (te.classification != null) {
                    bw.write(te.classification);
                }
                bw.write("\t");
                if (te.recordType != null) {
                    bw.write(te.recordType);
                }
                bw.write("\r\n");
            }
            bw.close();
            fw.close();
        } catch (IOException ioe) {
            System.out.println("Error creating audit report (AuditReport.txt): " + ioe.getMessage());
        }
    }

    /**
     * XML encode string
     *
     * Make sure any XML special characters in a string are encoded
     */
    private String XMLencode(String in) {
        StringBuffer out;
        int i;
        char c;

        if (in == null) {
            return null;
        }
        out = new StringBuffer();
        for (i = 0; i < in.length(); i++) {
            c = in.charAt(i);
            switch (c) {
                case '&':
                    if (!in.regionMatches(true, i, "&amp;", 0, 5)
                            && !in.regionMatches(true, i, "&lt;", 0, 4)
                            && !in.regionMatches(true, i, "&gt;", 0, 4)
                            && !in.regionMatches(true, i, "&quot;", 0, 6)
                            && !in.regionMatches(true, i, "&apos;", 0, 6)) {
                        out.append("&amp;");
                    }
                    break;
                case '<':
                    out.append("&lt;");
                    break;
                case '>':
                    out.append("&gt;");
                    break;
                case '"':
                    out.append("&quot;");
                    break;
                case '\'':
                    out.append("&apos;");
                    break;
                default:
                    out.append(c);
                    break;
            }
        }
        return (out.toString());
    }

    /**
     * versDateTime
     *
     * Returns a date and time in the standard VERS format (see PROS 99/007
     * (Version 2), Specification 2, p146
     *
     * @param ms	milliseconds since the epoch (if zero, return current
     * date/time)
     */
    private String versDateTime(long ms) {
        Date d;
        SimpleDateFormat sdf;
        TimeZone tz;
        Locale l;
        String s;

        tz = TimeZone.getDefault();
        sdf = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ssZ");
        sdf.setTimeZone(tz);
        if (ms == 0) {
            d = new Date();
        } else {
            d = new Date(ms);
        }
        s = sdf.format(d);
        return s.substring(0, 22) + ":" + s.substring(22, 24);

    }

    /**
     * TrimEntity
     *
     * Private class to represent a Trim Entity. Used to detect TRIM entities
     * that are referenced, but which do not exist, and entities that exist, but
     * are neither root element, nor referenced.
     */
    private class TrimEntity {

        TrimID id;          // id of TRIM entity
        String name;        // name of the TRIM entity (i.e. id converted to be safe)
        boolean root;       // true if a root entity
        boolean referenced; // true if referenced by another TRIM entity
        boolean defined;    // true if this entity exists
        boolean exported;   // true if entity was exported into a VEO
        StringBuffer referencedBy; // list of TRIM entity that reference this element
        String[] tokens;    // metadata about entity
        ArrayList<String> refs; // list of other TRIM entities this entity references
        Path dir;           // directory in which this TRIM entity is to be found
        String veoName;
        TrimID container;
        String title;
        String dateCreated;
        String dateRegistered;
        String classification;
        String recordType;
        String retentionSchedule;
        String contentFile;

        public TrimEntity(String id, String[] tokens, Path dir) throws Error {
            StringBuilder sb;
            int j;
            char c;

            this.id = new TrimID(id);
            sb = new StringBuilder();
            for (j = 0; j < id.length(); j++) {
                c = id.charAt(j);
                if (Character.isLetterOrDigit(c)) {
                    sb.append(c);
                } else {
                    sb.append('-');
                }
            }
            name = sb.toString();
            root = false;
            referenced = false;
            defined = false;
            exported = false;
            referencedBy = new StringBuffer();
            this.tokens = tokens;
            this.dir = dir;
            refs = new ArrayList<>();
            veoName = null;
            container = null;
            title = null;
            dateCreated = null;
            dateRegistered = null;
            classification = null;
            recordType = null;
            retentionSchedule = null;
            contentFile = null;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append("id:" + name);
            sb.append("\tparent:" + container);
            sb.append("\ttitle:" + title);
            sb.append("\tclass:" + classification);
            sb.append("\tretSch:" + retentionSchedule);
            return sb.toString();
        }
    }

    private class TrimID {

        String type;
        String year;
        int seq;

        public TrimID(String id) throws Error {
            String[] tokens;

            if (id == null) {
                throw new Error("Invalid TRIM ID: null pointer");
            }
            tokens = id.split("/");
            if (tokens.length != 3) {
                throw new Error("Invalid TRIM ID: '" + id + "': doesn't have three parts separated by '/'");
            }
            type = tokens[0];
            switch (tokens[1].length()) {
                case 2:
                    year = tokens[1];
                    break;
                case 4:
                    year = tokens[1].substring(2);
                    break;
                default:
                    throw new Error("Invalid TRIM ID: '" + id + "': year is not 2 or 4 digits in length (" + tokens[1] + ")");
            }
            try {
                seq = Integer.parseInt(tokens[2]);
            } catch (NumberFormatException nfe) {
                throw new Error("Invalid TRIM ID: '" + id + "': invalid sequence number: " + nfe.toString());
            }
        }

        public boolean equals(TrimID i) {
            if (!i.type.equals(type)) {
                return false;
            }
            if (!i.year.equals(year)) {
                return false;
            }
            if (i.seq != seq) {
                return false;
            }
            return true;
        }

        @Override
        public String toString() {
            return type + "/" + year + "/" + seq;
        }
    }

    /**
     * Main program
     *
     * @param args command line arguments
     */
    public static void main(String args[]) {
        TrimProcessV3CSV tp;

        try {
            tp = new TrimProcessV3CSV(args);
            tp.processExports();
            tp.report();
        } catch (VEOError e) {
            System.out.println(e.getMessage());
            System.exit(-1);
        }
    }
}
