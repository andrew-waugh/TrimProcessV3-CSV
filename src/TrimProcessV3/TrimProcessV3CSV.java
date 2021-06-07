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
import java.io.*;
import java.nio.file.*;
import java.util.TimeZone;
import java.util.Locale;
import java.util.Date;
import java.util.*;
import java.text.SimpleDateFormat;
import VEOCreate.CreateVEO;
import VEOCreate.Fragment;
import VERSCommon.AppError;
import VERSCommon.LTSF;
import VERSCommon.PFXUser;
import VERSCommon.VEOError;
import VERSCommon.VEOFatal;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
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
     * </pre>
     */
    static String version() {
        return ("2.00");
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
        int i;

        // Set up logging
        System.setProperty("java.util.logging.SimpleFormatter.format", "%4$s: %5$s%n");
        LOG.setLevel(Level.WARNING);
        // rootLog.setLevel(Level.WARNING);

        // set up default global variables
        files = new ArrayList<>();
        sourceDirectory = Paths.get(".");
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
        r = Runtime.getRuntime();

        // variables for processing this XML document
        labels = null;

        // process command line arguments
        configure(args);

        // tell what is happening
        LOG.log(Level.INFO, "******************************************************************************");
        LOG.log(Level.INFO, "*                                                                            *");
        LOG.log(Level.INFO, "*     T R I M   C V S   E X P O R T ( V 3 )   C R E A T I O N   T O O L      *");
        LOG.log(Level.INFO, "*                                                                            *");
        LOG.log(Level.INFO, "*                                Version " + version() + "                                *");
        LOG.log(Level.INFO, "*            Copyright 2015, 2021 Public Record Office Victoria              *");
        LOG.log(Level.INFO, "*                                                                            *");
        LOG.log(Level.INFO, "******************************************************************************");
        LOG.log(Level.INFO, "");
        LOG.log(Level.INFO, "Run at ");
        tz = TimeZone.getTimeZone("GMT+10:00");
        sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss+10:00");
        sdf.setTimeZone(tz);
        LOG.log(Level.INFO, sdf.format(new Date()));
        LOG.log(Level.INFO, "");
        if (help) {
            // trimProcessV3 -t <directory> -s <pfxFile> <password> -support <directory> [-v] [-d] [-h hashAlg] [-o <directory>] [-a dir]* [-rev] (files|directories)*
            LOG.log(Level.INFO, "Command line arguments:");
            LOG.log(Level.INFO, " Mandatory:");
            LOG.log(Level.INFO, "  -s <pfxFile> <password>: path to a PFX file and its password for signing a VEO");
            LOG.log(Level.INFO, "  -suppport <directory>: path to a directory containing V3 support files (the LTSF definition)");
            LOG.log(Level.INFO, "  files or directories: locations to find the TRIM CSV/content export");
            LOG.log(Level.INFO, "");
            LOG.log(Level.INFO, " Optional:");
            LOG.log(Level.INFO, "  -t <directory>: file path to where the templates are located");
            LOG.log(Level.INFO, "  -h <hashAlgorithm>: specifies the hash algorithm (default SHA-256)");
            LOG.log(Level.INFO, "  -o <directory>: the directory in which the VEOs are created (default is current working directory)");
            LOG.log(Level.INFO, "  -rev: include all revisions of the content (if present)");
            LOG.log(Level.INFO, "");
            LOG.log(Level.INFO, "  -v: verbose mode: give more details about processing");
            LOG.log(Level.INFO, "  -d: debug mode: give a lot of details about processing");
            LOG.log(Level.INFO, "  -help: print this listing");
            LOG.log(Level.INFO, "");
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
        if (supportDir == null) {
            throw new VEOFatal("You must specify a VERS support directory using the -suppoort command line argument");
        }
        if (templateDir == null) {
            throw new VEOFatal("You must specify a template directory using the -t command line argument");
        }

        // LOG generic things
        if (debug) {
            LOG.log(Level.INFO, "Debug mode is selected");
        }
        if (verbose) {
            LOG.log(Level.INFO, "Verbose output is selected");
        }
        if (incRevisions) {
            LOG.log(Level.INFO, "Including revisions");
        }
        LOG.log(Level.INFO, "Hash algorithm is ''{0}''", hashAlg);
        if (templateDir != null) {
            LOG.log(Level.INFO, "Common AGLS metadata & VEOReadme.txt from ''{0}''", new Object[]{templateDir.toString()});
        } else {
            LOG.log(Level.INFO, "No common AGLS metadata specified");
        }
        LOG.log(Level.INFO, "RDF Identifier prefix is ''{0}''", rdfIdPrefix);
        LOG.log(Level.INFO, "Source directory is ''{0}''", new Object[]{sourceDirectory.toString()});
        LOG.log(Level.INFO, "Output directory is ''{0}''", new Object[]{outputDirectory.toString()});
        LOG.log(Level.INFO, "Template directory is ''{0}''", new Object[]{templateDir.toString()});
        LOG.log(Level.INFO, "Support directory is ''{0}''", new Object[]{supportDir.toString()});
        LOG.log(Level.INFO, "User id to be logged: ''{0}''", new Object[]{userId});
        LOG.log(Level.INFO, "PFX user is ''{0}''", new Object[]{user.getUserId()});

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
        String usage = "trimProcessV3 -t <directory> -s <pfxFile> <password> -support <directory> [-v] [-d] [-h hashAlg] [-o <directory>] [-a dir]* [-rev] (files|directories)*";

        // process command line arguments
        i = 0;
        try {
            while (i < args.length) {
                switch (args[i]) {

                    // verbose?
                    case "-v":
                        verbose = true;
                        LOG.setLevel(Level.INFO);
                        // rootLog.setLevel(Level.INFO);
                        i++;
                        break;

                    // debug?
                    case "-d":
                        debug = true;
                        LOG.setLevel(Level.FINE);
                        // rootLog.setLevel(Level.FINE);
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

                    // '-o' specifies output directory
                    case "-o":
                        i++;
                        outputDirectory = checkFile("output directory", args[i], true);
                        i++;
                        break;

                    // '-source' specifies output directory
                    case "-source":
                        i++;
                        sourceDirectory = checkFile("source directory", args[i], true);
                        i++;
                        break;

                    // '-support' specifies output directory
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

                        // if doesn't start with '-' assume a file or directory name
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
     */
    public void processExports() {
        int i;
        String file;

        // go through the list of files
        freemem = r.freeMemory();
        for (i = 0; i < files.size(); i++) {
            file = files.get(i);
            if (file == null) {
                continue;
            }
            processFile(sourceDirectory.resolve(file));
        }
    }

    /**
     * ProcessFile
     *
     * This method checks to see if this is an XML file, in which case it
     * processes it, otherwise if it is a directory, it recurses into it.
     */
    private void processFile(Path f) {
        DirectoryStream<Path> ds;
        SortedMap<String, TrimEntity> entities; // record of entities found or referenced

        // check that file or directory exists
        if (!Files.exists(f)) {
            LOG.log(Level.WARNING, "***File ''{0}'' does not exist", new Object[]{f.toString()});
            return;
        }

        // if file is a directory, go through directory and test all the files
        if (Files.isDirectory(f)) {
            LOG.log(Level.INFO, "***Processing directory ''{0}''", new Object[]{f.toString()});
            try {
                ds = Files.newDirectoryStream(f);
                for (Path p : ds) {
                    processFile(Paths.get(p.toString()));
                }
                ds.close();
            } catch (IOException e) {
                LOG.log(Level.WARNING, "Failed to process directory ''{0}'': {1}", new Object[]{f.toString(), e.getMessage()});
            }
            return;
        }

        // is this file a TRIM entity file?
        if (Files.isRegularFile(f)) {
            // convert the TRIM entity file into a set of TRIM entities & process them
            try {
                entities = readTrimEntityFile(f);
                if (entities != null) {
                    processTrimEntities(entities);
                }
                rememberTrimEntities(entities, f.getParent());
            } catch (VEOError e) {
                LOG.log(Level.WARNING, "***Ignoring TRIM entity file  ''{0}'': {1}", new Object[]{f.toString(), e.getMessage()});
            }
        } else if (debug) {
            LOG.log(Level.INFO, "***Ignoring file  ''{0}''", new Object[]{f.toString()});
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
    private SortedMap<String, TrimEntity> readTrimEntityFile(Path f) throws VEOError {
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
            throw new VEOError("Processing TRIM entity file: failed because could not open parent directory");
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
                    System.out.println("Columns:" + tokens.length);
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
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Expanded Number' column");
                    }
                    if (containerCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Container' column");
                    }
                    /*
                    if (containedCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find '*Contained Records*' column");
                    }
                     */
                    if (titleCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Title (Free Text Part)' column");
                    }
                    if (classificationCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Classification' column");
                    }
                    if (dateCreatedCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Date Created' column");
                    }
                    if (dateRegisteredCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Date Registered' column");
                    }
                    if (recordTypeCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Record Type' column");
                    }
                    /*
                    if (isPartCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find '*Is Part*' column");
                    }
                     */
                    if (docFileCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'DOS File' column");
                    }
                    if (retSchCol == -1) {
                        throw new VEOError("Error reading '" + f.toRealPath().toString() + "': Could not find 'Retention schedule' column");
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
                    te.dateRegistered = tokens[dateRegisteredCol];
                    te.classification = tokens[classificationCol];
                    switch (tokens[recordTypeCol]) {
                        case "CABINET FILE":
                            te.recordType = "Cabinet File";
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
                        case "MINISTERIAL CORRESPONDENCE  - VERS":
                            te.recordType = "Ministerial Correspondence - VERS";
                            break;
                        default:
                            System.out.println("WARNING: Unhandled record type: '" + tokens[recordTypeCol] + "'");
                            te.recordType = tokens[recordTypeCol];
                            break;
                    }
                    te.retentionSchedule = tokens[retSchCol];
                    System.out.println(te.toString());
                }
                lineNo++;
            }
        } catch (FileNotFoundException fnfe) {
            LOG.log(Level.INFO, "TRIM entity file ''{0}'' does not exist", new Object[]{f.toAbsolutePath().toString()});
        } catch (IOException ioe) {
            LOG.log(Level.INFO, "Error when reading TRIM entity file ''{0}'': ''{1}''", new Object[]{f.toAbsolutePath().toString(), ioe.getMessage()});
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

            // ignore this entry if it is not a root entry
            if (te.tokens[containerCol] == null || te.tokens[containerCol].equals("")) {
                te.root = true;
                try {
                    createVEO(te, entities);
                } catch (VEOError | AppError e) {
                    LOG.log(Level.WARNING, "Failed to build VEO ''{0}'' because {1}", new Object[]{key, e.getMessage()});
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
        StringBuilder res;

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
        LOG.log(Level.INFO, "{0} Processing: {1}", new Object[]{(new Date()).getTime() / 1000, base.name});
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
        res = new StringBuilder();
        cv = new CreateVEO(outputDirectory, recordName, hashAlg, verbose);
        try {
            cv.addVEOReadme(supportDir);
            cv.addEvent(versDateTime(System.currentTimeMillis()), "Converted to VEO", userId, description, errors);
            processTrimEntity(base, entities, cv, recordName, 1, recordName + ".veo.zip", res);
            if (res.length() != 0) {
                if (res.charAt(res.length() - 1) == '\n') {
                    res.setCharAt(res.length() - 1, ' ');
                }
                LOG.log(Level.WARNING, "VEO ''{0}.veo.zip'' incomplete because:\n{1}", new Object[]{recordName, res.toString()});
            }
            cv.finishFiles();
            cv.sign(user, hashAlg);
            cv.finalise(true);
        } catch (VEOError ve) {
            cv.abandon(true);
            throw ve;
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
    private void processTrimEntity(TrimEntity base, SortedMap<String, TrimEntity> entities, CreateVEO cv, String recordName, int depth, String veoName, StringBuilder res) throws VEOError, AppError {
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
            if (base.tokens[docFileCol] != null && !base.tokens[docFileCol].equals("")) {

                // get the content files for this TRIM entity. There will be two
                // file names, separated by a '|'. The first is the internal TRIM
                // file name, the second appears to be the original file name.
                // We use the second one...
                contents = base.tokens[docFileCol].replace('|', '\t').split("\t");
                if (contents.length == 2) {
                    i = 1;
                } else {
                    i = 0;
                }

                // add an information piece with a single content file
                String veoRef = (recordName.replace('/', '-') + "/" + contents[i]);
                p = sourceDirectory.resolve(contents[i]);
                try {
                    cv.addInformationPiece(null);
                    cv.addContentFile(veoRef, p);
                } catch (VEOError e) {
                    res.append("Information Object " + base.name + " is incomplete because: ");
                    res.append(e.getMessage());
                    res.append("\n");
                }

                /* this export doesn't include renditions or attachements
                    for (i = 0; i < attachments.size(); i++) {
                        cv.addContentFile(recordName + "/" + attachments.get(i));
                    }
                    for (i = 0; i < renditions.size(); i++) {
                        cv.addContentFile(recordName + "/" + renditions.get(i).file);
                        isLTPF |= isLTPF(renditions.get(i).file);
                    }
                 */
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
                            res.append("Failed attempting to add DummyContentFile: " + ioe.getMessage());
                        }
                    }
                    veoRef = (recordName.replace('/', '-') + "/DummyContentFile.txt");
                    cv.addContentFile(veoRef, dummyLTSFCF);
                }
            }

            // add versions of the record if requested
            /*
            if (incRevisions) {
                for (i = 0; i < revisions.size(); i++) {
                    cv.addInformationPiece("Revision");
                    cv.addContentFile(recordName + "/" + revisions.get(i).file);
                }
            }
            // exported correctly
            currentEntity.exported = true;
             */
            // extract the TRIM entities contained in this TRIM entity and
            // record them. The processing is tedious. The
            // contained entities are encoded in a string, separated by the
            // literal characters '\r\n'. Each reference is the TRIM id, a ':',
            // and the name. The TRIM id has a two digit year, instead of the 
            // four digit year used elsewhere. UGGGH.
            /*
            s = base.tokens[containedCol];
            if (s != null && !s.equals("")) {
                contents = s.split("\\\\r\\\\n");
                for (i = 0; i < contents.length; i++) {
                    if ((j = contents[i].indexOf(':')) == -1) {
                        continue;
                    }
                    s = contents[i].substring(0, j - 1);
                    name = s.split("/");
                    switch (name.length) {
                        case 2:
                            s = "20" + name[0] + "/" + name[1];
                            break;
                        case 3:
                            s = name[0] + "/20" + name[1] + "/" + name[2];
                            break;
                        default:
                            throw new VEOError("Unknown file reference: '" + s);
                    }
                    base.refs.add(s);
                }
            }
             */
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
                    processTrimEntity(t, entities, cv, t.tokens[idCol].trim(), depth + 1, veoName, res);
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
     * Copy a content file into the VEO content directory
     *
     */
    private Path copyContentFile(TrimEntity base, String srcfn, Path destDir, String destfn) throws VEOError {
        Path source, destination;

        // get the source of the copy
        if (srcfn == null || srcfn.equals("")) {
            throw new VEOError("Copying DOS content file from entity failed as the content file name is null");
        }
        source = Paths.get(base.dir.toString(), srcfn);
        if (!Files.exists(source)) {
            throw new VEOError("TRIM entity content: '" + source.toString() + "' does not exist");
        }
        if (Files.isDirectory(source)) {
            throw new VEOError("TRIM entity content: '" + source.toString() + "' is a directory not a file");
        }

        // get the destination directory
        destination = Paths.get(destDir.toString(), destfn);

        // copy
        try {
            Files.copy(source, destination, StandardCopyOption.COPY_ATTRIBUTES);
        } catch (IOException ioe) {
            throw new VEOError("Copying: '" + source.toString() + "' to VEO failed: " + ioe.getMessage());
        }

        return Paths.get(destfn);
    }

    /**
     * Convert a VMBX file into a text file containing the email body and one or
     * more embedded files
     */
    /*
    private void processVMBXfile(String value) {
        StringReader sr;    // for breaking value into lines
        BufferedReader br;
        PrintWriter fw;     // for writing the email body
        BufferedWriter bw;
        FileOutputStream fos1; // for writing Base64 encoded attachments
        BufferedOutputStream bos1;
        Path p, p1;
        String line, fileName;
        char[] cb;
        int state;

        // open writer for writing the email body
        p = Paths.get(contentDirectory.toString(), "final.txt");
        try {
            fw = new PrintWriter(p.toString());
        } catch (IOException fnfe) {
            LOG.log(Level.WARNING, "Arrgh: Could not create: ''{0}'': {1}", new Object[]{p.toString(), fnfe.getMessage()});
            return;
        }
        bw = new BufferedWriter(fw);

        // open output stream for decoded base64 attachments
        fos1 = null;
        bos1 = null;

        // read value line by line
        sr = new StringReader(value);
        br = new BufferedReader(sr);
        state = 0;
        try {
            while ((line = br.readLine()) != null) {
                switch (state) {
                    case 0: // processing the header until we see the start of a embedded object
                        fw.println(line);
                        if (line.startsWith("====Embedded====")) {
                            fileName = line.substring(17);
                            fw.println("Embedded file has been extracted to file '" + fileName + "'");
                            attachments.add(fileName);
                            p1 = Paths.get(contentDirectory.toString(), fileName);
                            fos1 = new FileOutputStream(p1.toString());
                            bos1 = new BufferedOutputStream(fos1);
                            state = 1;
                        }
                        break;
                    case 1: // seen an embedded line, now processing the Base64 encodings
                        if (line.startsWith("====Embedded====")) {
                            if (bos1 != null) {
                                bos1.close();
                            }
                            if (fos1 != null) {
                                fos1.close();
                            }
                            fw.println(line);
                            fileName = line.substring(17);
                            fw.println("Embedded file has been extracted to file '" + fileName + "'");
                            attachments.add(fileName);
                            p1 = Paths.get(contentDirectory.toString(), fileName);
                            fos1 = new FileOutputStream(p1.toString());
                            bos1 = new BufferedOutputStream(fos1);
                        } else {
                            cb = line.toCharArray();
                            b64.fromBase64(cb, 0, cb.length, bos1);
                        }
                        break;
                }
            }
            if (bos1 != null) {
                bos1.close();
            }
            if (fos1 != null) {
                fos1.close();
            }
            bw.close();
            fw.close();
            sr.close();
            br.close();
        } catch (IOException ioe) {
            LOG.log(Level.WARNING, "Arrgh: IOException when extracting the VMBX file: {0}", new Object[]{ioe.getMessage()});
        }
    }
     */
    /**
     * Function to process the TRIM date into an ISO8601 date. The TRIM date has
     * the format [d]d/mm/yyyy_at_[h]h:mm_[A|P]M Note that the first digit of
     * the day and the hour is not present if it should be '0'.
     *
     * @param date the TRIM date
     * @return the ISO8601 date
     */
    private String processOldDate(String date) {
        int i, p;
        String s, year, month, day, hour, min;

        if (date == null) {
            return null;
        }
        if (date.charAt(1) == '/') {
            day = '0' + date.substring(0, 1);
            p = 2;
        } else {
            day = date.substring(0, 2);
            p = 3;
        }
        if (date.charAt(p + 1) == '/') {
            month = '0' + date.substring(p, p + 1);
            p += 2;
        } else {
            month = date.substring(p, p + 2);
            p += 3;
        }
        year = date.substring(p, p + 4);
        if (date.length() < 11) {
            s = year + "-" + month + "-" + day;
        } else {
            if (date.charAt(p + 1) == ':') {
                i = Integer.parseInt(date.substring(p, p + 1));
                p += 2;
            } else {
                i = Integer.parseInt(date.substring(p, p + 2));
                p += 3;
            }
            if (date.charAt(p + 3) == 'P') {
                i += 12;
            }
            hour = Integer.toString(i);
            min = date.substring(p, p + 2);
            s = year + "-" + month + "-" + day + "T" + hour + ":" + min;
        }
        return s;
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
        ZonedDateTime now = ZonedDateTime.now();
        DateTimeFormatter dtf;
        int i;

        // Ouput report
        System.out.println("REPORT FOR PROCESSING TRIM EXPORT");
        dtf = DateTimeFormatter.ofPattern("dd MMMM yyyy',' HHmm 'hours' (XX)");
        System.out.println("Processing performed at " + now.format(dtf) + " by " + userId);
        System.out.print("TRIM export files located in: ");
        for (i = 0; i < files.size(); i++) {
            System.out.print("'" + files.get(i) + "'");
            if (i < files.size() - 1) {
                System.out.print(", ");
            }
        }
        System.out.println();
        if (incRevisions) {
            System.out.println("Revisions contained in TRIM export have been included");
        } else {
            System.out.println("Revisions contained in TRIM export have been discarded");
        }
        System.out.println("Hash algorithm is " + hashAlg);
        System.out.println("Source directory is '" + sourceDirectory.toAbsolutePath().toString() + "'");
        System.out.println("Output directory is '" + outputDirectory.toAbsolutePath().toString() + "'");
        System.out.println("Template directory is '" + templateDir.toAbsolutePath().toString() + "'");
        System.out.println("PFX user is '" + user.getUserId() + "'");

        System.out.println("Total records (VEOs) created: " + exportCount);
        System.out.println("");

        // output all
        /*
        it = allEntities.keySet().iterator();
        anyFound = false;
        System.out.println();
        System.out.println("TRIM Entities:");
        while (it.hasNext()) {
            te = allEntities.get(it.next());
            System.out.println("\t" + te.id + " r:" + te.root + " d:" + te.defined + " e:"+te.exported);
        }
         */
        // Entities that were referenced, but not included in export
        /* Not used as this export doesn't list children
        it = allEntities.keySet().iterator();
        anyFound = false;
        System.out.println();
        System.out.println("TRIM Entities referenced as children, but which did not exist as files in export:");
        while (it.hasNext()) {
            te = allEntities.get(it.next());
            if (te.referenced && !te.defined) {
                System.out.println("\t" + te.id + " in " + te.dir.toString() + " (referenced by " + te.referencedBy.toString() + ")");
                anyFound = true;
            }
        }
        if (!anyFound) {
            System.out.println("\tNo entities");
        }
        it = allEntities.keySet().iterator();
        anyFound = false;
        System.out.println();

        // entities in export that were not part of files
        System.out.println("TRIM Entities which exist in export, but which are not part of files:");
        while (it.hasNext()) {
            te = allEntities.get(it.next());
            if (te.defined && !(te.root || te.referenced)) {
                System.out.println("\t" + te.id + " in " + te.dir.toString());
                anyFound = true;
            }
        }
        if (!anyFound) {
            System.out.println("\tNo entities");
        }
        System.out.println();
         */
        // Report on root entities
        it = allEntities.keySet().iterator();
        anyFound = false;
        System.out.println("Files (VEOs) generated:");
        while (it.hasNext()) {
            te = allEntities.get(it.next());
            if (te.defined && te.root) {
                System.out.println("\t" + te.id + " in " + te.dir.toString());
                // System.out.println("\t" + te.id + " " + te.dateCreated + " (" + te.title + ")");
                anyFound = true;
            }
        }
        if (!anyFound) {
            System.out.println("\tNo entities");
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
     * HandleDataFailures
     *
     * This class allows the archivist to gracefully handle data failures: 1)
     * TRIM entities that are missing 2) TRIM entities that are so malformed
     * they cannot be fixed 3) Data content that has no long term preservation
     * format
     *
     * The core is the problemReport.txt file. If this is present in the output
     * directory, the contents are read into this class. If a problem is found
     * with a TRIM entity, the entity is looked up, and if a custom explanation
     * file is specified, it is read and included in the VEO as the IO.
     * Otherwise the default explanation is used and the problem is recorded. At
     * the end of the program, the original problemReport.txt file is replaced.
     */
    private class TRIMEntityHandler {

        Path problemReport;     // name and location of the problem report file
        TreeMap<String, TRIMEntityProblem> problemEntities; // list of problem entities we have seen

        // construct from the problemReport.txt file if it exists
        public TRIMEntityHandler(Path problemReport) {
            FileReader fr = null;
            BufferedReader br = null;
            String line;
            String[] tokens;
            TRIMEntityProblem tep;

            this.problemReport = problemReport;
            problemEntities = new TreeMap<>();

            // if the problem report exists, open it and read it
            if (Files.exists(problemReport)) {
                try {
                    fr = new FileReader(problemReport.toFile());
                    br = new BufferedReader(fr);
                    while ((line = br.readLine()) != null) {
                        tokens = line.split("\t");
                        if (tokens.length != 3) {
                            LOG.log(Level.INFO, "Problem report file ''{0}'' line ''{1}'' does not have three tokens", new Object[]{problemReport.toString(), line});
                            continue;
                        }
                        tep = new TRIMEntityProblem(tokens[0], tokens[1], tokens[2]);
                        problemEntities.put(tokens[0], tep);
                    }
                } catch (FileNotFoundException fnfe) {
                    LOG.log(Level.INFO, "Problem Report file unexpectedly does not exist", new Object[]{fnfe.getMessage()});
                } catch (IOException ioe) {
                    LOG.log(Level.INFO, "Error when reading Problem Report file ''{0}'': ''{1}''", new Object[]{problemReport.toString(), ioe.getMessage()});
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
            }
        }

        // Look up a TRIM entity that is having problems...
        public String lookup(String id, TRIMEntityProblemTypes problemType, String problem) {
            TRIMEntityProblem tep;

            tep = problemEntities.get(id);

            // if it doesn't exist, remember this problem
            if (tep == null) {
                switch (problemType) {
                    case MISSING:
                        tep = new TRIMEntityProblem(id, "MissingTRIMEntity.txt", problem);
                        break;
                    case MALFORMED:
                        tep = new TRIMEntityProblem(id, "MalformedTRIMEntity.txt", problem);
                        break;
                    case MISSING_LTPF:
                        tep = new TRIMEntityProblem(id, "NoLTPFInTRIMEntity.txt", problem);
                        break;
                    default:
                        LOG.log(Level.SEVERE, "Undefined problem type in TRIMEntity.lookup");
                        tep = new TRIMEntityProblem(id, "NoLTPFInTRIMEntity.txt", problem); // wrong, but won't cause a failure
                }
                tep.seenNow = true;
            } else {

            }
            return tep.file;
        }

        // write the problem report out
        public boolean writeReport() {
            Iterator<String> it;
            FileWriter fw;
            BufferedWriter bw;
            TRIMEntityProblem tep;
            Path tmp;

            // try to move existing problemReport.txt
            if (Files.exists(problemReport)) {
                // tmp = Files.move(problemReport, tmp, cos)
            }
            try {
                fw = new FileWriter(problemReport.toFile());
                bw = new BufferedWriter(fw);

                it = problemEntities.keySet().iterator();
                while (it.hasNext()) {
                    tep = problemEntities.get(it.next());
                    bw.write(tep.id);
                    bw.write("\t");
                    bw.write(tep.file);
                    bw.write("\t");
                    bw.write(tep.error);
                    bw.write("\r\n");
                }
                bw.close();
                fw.close();
            } catch (IOException ioe) {
                System.out.println("Error creating error report (AuditReport.txt): " + ioe.getMessage());
            }
            return true;
        }
    }

    public enum TRIMEntityProblemTypes {
        MISSING, // TRIM entity is not present in export
        MALFORMED, // TRIM entity cannot be parsed
        MISSING_LTPF    // Content has no LTPF
    };

    /**
     * Private class recording a TRIM entity problem
     */
    private class TRIMEntityProblem {

        String id;      // id of the TRIM Entity
        String file;    // file containing explanation
        String error;   // description of error
        boolean seenNow;  // true if this problem was seen in this run

        public TRIMEntityProblem(String id, String file, String error) {
            this.id = id;
            this.file = file;
            this.error = error;
            seenNow = false;
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
