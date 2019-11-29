package TrimProcessV3;

/**
 *
 * B 6 4
 *
 * Andrew Waugh, May 2006
 *
 * This class encapsulates routines to encode and decode from Base64 Base64 is
 * defined in RFC 2045 Multipurpose Internet Mail Extensions (MIME) Part One:
 * Format of Internet Message Bodies, section 6.8.
 *
 *
 */
import java.io.*;

public class B64 {

    private static final char[] charMapEnc = {
        'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H',
        'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P',
        'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X',
        'Y', 'Z', 'a', 'b', 'c', 'd', 'e', 'f',
        'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n',
        'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
        'w', 'x', 'y', 'z', '0', '1', '2', '3',
        '4', '5', '6', '7', '8', '9', '+', '/'};

    /**
     * Constructor
     */
    public B64() {
    }

    /**
     * Encode the data in a file into Base64.
     *
     * @param	in	the InputStream containing the data
     * @param bw the Writer that gets the Base64
     * @throws	IOException
     */
    public void toBase64(InputStream in, Writer bw)
            throws IOException {
        int i, j, c;
        byte[] bin, bout;
        BufferedInputStream bis;

        bis = new BufferedInputStream(in);
        bin = new byte[3];
        bout = new byte[4];
        c = 1;
        while (c != -1) {
            for (i = 0; i < 19; i++) {
                c = bis.read(bin);
                if (c == -1) {
                    break;
                }
                if (c == 1) {
                    bin[1] = 0;
                    bin[2] = 0;
                }
                if (c == 2) {
                    bin[2] = 0;
                }
                bout[0] = (byte) ((bin[0] & 0xFC) >> 2);
                bout[1] = (byte) (((bin[0] & 0x03) << 4) | ((bin[1] & 0xF0) >> 4));
                bout[2] = (byte) (((bin[1] & 0x0F) << 2) | ((bin[2] & 0xC0) >> 6));
                bout[3] = (byte) (bin[2] & 0x3F);
                bw.write(charMapEnc[bout[0]]);
                bw.write(charMapEnc[bout[1]]);
                if (c > 1) {
                    bw.write(charMapEnc[bout[2]]);
                } else {
                    bw.write('=');
                }
                if (c > 2) {
                    bw.write(charMapEnc[bout[3]]);
                } else {
                    bw.write('=');
                }
            }
            bw.write('\n');
        }
        bis.close();
    }

    /**
     * Encode the data in a byte array into Base64 returning a String.
     *
     * @param	in	the byte array containing the data
     * @return	the string containing the Base64
     */
    public String toBase64(byte[] in) {
        int i, j, x, c;
        byte[] bin, bout;
        ByteArrayOutputStream boas;
        StringBuffer sb;

        boas = new ByteArrayOutputStream();
        sb = new StringBuffer();
        bin = new byte[3];
        bout = new byte[4];
        x = 0;
        while (x < in.length) {
            for (i = 0; i < 19; i++) {
                if (x == in.length) {
                    break;
                }
                bin[0] = in[x++];
                c = 1;
                if (x < in.length) {
                    bin[1] = in[x++];
                    c = 2;
                } else {
                    bin[1] = 0;
                }
                if (x < in.length) {
                    bin[2] = in[x++];
                    c = 3;
                } else {
                    bin[2] = 0;
                }
                bout[0] = (byte) ((bin[0] & 0xFC) >> 2);
                bout[1] = (byte) (((bin[0] & 0x03) << 4) | ((bin[1] & 0xF0) >> 4));
                bout[2] = (byte) (((bin[1] & 0x0F) << 2) | ((bin[2] & 0xC0) >> 6));
                bout[3] = (byte) (bin[2] & 0x3F);
                sb.append(charMapEnc[bout[0]]);
                sb.append(charMapEnc[bout[1]]);
                if (c > 1) {
                    sb.append(charMapEnc[bout[2]]);
                } else {
                    sb.append('='); // ASCII for '='
                }
                if (c > 2) {
                    sb.append(charMapEnc[bout[3]]);
                } else {
                    sb.append('=');
                }
            }
            sb.append('\n');
        }
        return sb.toString();
    }

    private static final byte[] charMapDec = {
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // 00
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // 10
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 62, 64, 64, 64, 63, // 20
        52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 64, 64, 64, 00, 64, 64, // 30
        64, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, // 40
        15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 64, 64, 64, 64, 64, // 50
        64, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, // 60
        41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 64, 64, 64, 64, 64, // 70
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // 80
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // 90
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // a0
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // b0
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // c0
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // d0
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, // e0
        64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64 // f0
    };

    /**
     * Decode the data in a StringBuilder from Base64.
     *
     * @param	in	the StringBuilder containing the encoded data
     * @param	out	the OutputStream for the plaintext data
     * @throws	IOException
     */
    public void fromBase64(StringBuilder in, OutputStream out) throws IOException {
        int i, j, pad, c;
        byte b;
        byte[] bin, bout;
        BufferedOutputStream bos;

        bos = new BufferedOutputStream(out);
        bin = new byte[4];
        bout = new byte[3];

        i = 0;
        pad = 0;
        for (j = 0; j < in.length(); i++) {
            c = in.charAt(j);
            b = charMapDec[c];
            if (c == '=') {
                pad++;
            }
            // System.err.print(c+" "+b+" ("+i+") ");
            if (b == 64) {
                continue;
            }
            bin[i] = (byte) b;
            i++;
            if (i == 4) {
                bout[0] = (byte) (((bin[0] & 0x3f) << 2) | ((bin[1] & 0x30) >> 4));
                bout[1] = (byte) (((bin[1] & 0x0f) << 4) | ((bin[2] & 0x3c) >> 2));
                bout[2] = (byte) (((bin[2] & 0x03) << 6) | (bin[3] & 0x3f));
                bos.write(bout[0]);
                if (pad < 2) {
                    bos.write(bout[1]);
                }
                if (pad < 1) {
                    bos.write(bout[2]);
                }
                i = 0;
            }
        }
        bos.close();
    }

    /**
     * Decode the data in a file from Base64.
     *
     * @param	in	the InputStream containing the encoded data
     * @param	out	the OutputStream for the plaintext data
     * @throws	IOException
     */
    public void fromBase64(Reader in, OutputStream out) throws IOException {
        int i, pad, c;
        byte b;
        byte[] bin, bout;
        BufferedOutputStream bos;

        bos = new BufferedOutputStream(out);
        bin = new byte[4];
        bout = new byte[3];

        i = 0;
        pad = 0;
        while ((c = in.read()) != -1) {
            b = charMapDec[c];
            if (c == '=') {
                pad++;
            }
            // System.err.print(c+" "+b+" ("+i+") ");
            if (b == 64) {
                continue;
            }
            bin[i] = (byte) b;
            i++;
            if (i == 4) {
                bout[0] = (byte) (((bin[0] & 0x3f) << 2) | ((bin[1] & 0x30) >> 4));
                bout[1] = (byte) (((bin[1] & 0x0f) << 4) | ((bin[2] & 0x3c) >> 2));
                bout[2] = (byte) (((bin[2] & 0x03) << 6) | (bin[3] & 0x3f));
                bos.write(bout[0]);
                if (pad < 2) {
                    bos.write(bout[1]);
                }
                if (pad < 1) {
                    bos.write(bout[2]);
                }
                i = 0;
            }
        }
        bos.close();
    }

    /**
     * Decode the data in a byte array from Base64, returning a byte array.
     *
     * @param	in	the byte array containing the encoded data
     * @return converted byte array
     * @throws	IOException
     */
    public byte[] fromBase64(byte[] in) throws IOException {
        int i, j, pad;
        byte b;
        byte[] bin, bout;
        ByteArrayOutputStream baos;

        baos = new ByteArrayOutputStream();
        bin = new byte[4];
        bout = new byte[3];

        i = 0;
        j = 0;
        pad = 0;
        for (j = 0; j < in.length; j++) {
            b = charMapDec[in[j]];
            if (in[j] == 61) {
                pad++; // ASCII for '='
            }
            if (b == 64) {
                continue;
            }
            // System.err.print("'"+((char) in[j])+"' ("+in[j]+") "+b+" ("+i+") "+pad+"\n");
            bin[i] = (byte) b;
            i++;
            if (i == 4) {
                bout[0] = (byte) (((bin[0] & 0x3f) << 2) | ((bin[1] & 0x30) >> 4));
                bout[1] = (byte) (((bin[1] & 0x0f) << 4) | ((bin[2] & 0x3c) >> 2));
                bout[2] = (byte) (((bin[2] & 0x03) << 6) | (bin[3] & 0x3f));
                baos.write(bout[0]);
                if (pad < 2) {
                    baos.write(bout[1]);
                }
                if (pad < 1) {
                    baos.write(bout[2]);
                }
                i = 0;
            }
        }
        baos.close();
        return baos.toByteArray();
    }

    /**
     * Decode the data in a character array from Base64 and write it to an
     * output Stream
     *
     * @param	in	the character array containing the encoded data
     * @param	start	start position in array
     * @param	length	length of valid characters
     * @param	out	the output stream
     * @throws	IOException
     */
    int si;				// current index into sbin
    byte[] sbin = {0, 0, 0, 0};	// static array for decoding. Needed because
    // arrays passed into this method may not end
    // on 3 byte boundaries

    public void reset() {
        si = 0;
    }

    /*
    public void fromBase64(String in, OutputStream out)
            throws IOException {
        int j, pad;
        byte b;
        byte[] bout;

        bout = new byte[3];

        j = 0;
        pad = 0;
        for (j = 0; j < in.length(); j++) {
            if (in[j] < 0 || in[j] > 255) {
                b = 64;
            } else {
                b = charMapDec[in[j]];
            }
            if (in[j] == 61) {
                pad++; // ASCII for '='
            }
            if (b == 64) {
                continue;
            }
            // System.err.print("'"+((char) in[j])+"' ("+in[j]+") "+b+" ("+j+") "+pad+"\n");
            sbin[si] = (byte) b;
            si++;
            if (si == 4) {
                bout[0] = (byte) (((sbin[0] & 0x3f) << 2) | ((sbin[1] & 0x30) >> 4));
                bout[1] = (byte) (((sbin[1] & 0x0f) << 4) | ((sbin[2] & 0x3c) >> 2));
                bout[2] = (byte) (((sbin[2] & 0x03) << 6) | (sbin[3] & 0x3f));
                out.write(bout[0]);
                if (pad < 2) {
                    out.write(bout[1]);
                }
                if (pad < 1) {
                    out.write(bout[2]);
                }
                si = 0;
            }
        }
    }
*/

    public void fromBase64(char[] in, int start, int length, OutputStream out)
            throws IOException {
        int j, pad;
        byte b;
        byte[] bout;

        bout = new byte[3];

        j = 0;
        pad = 0;
        for (j = start; j < start + length; j++) {
            if (in[j] < 0 || in[j] > 255) {
                b = 64;
            } else {
                b = charMapDec[in[j]];
            }
            if (in[j] == 61) {
                pad++; // ASCII for '='
            }
            if (b == 64) {
                continue;
            }
            // System.err.print("'"+((char) in[j])+"' ("+in[j]+") "+b+" ("+j+") "+pad+"\n");
            sbin[si] = (byte) b;
            si++;
            if (si == 4) {
                bout[0] = (byte) (((sbin[0] & 0x3f) << 2) | ((sbin[1] & 0x30) >> 4));
                bout[1] = (byte) (((sbin[1] & 0x0f) << 4) | ((sbin[2] & 0x3c) >> 2));
                bout[2] = (byte) (((sbin[2] & 0x03) << 6) | (sbin[3] & 0x3f));
                out.write(bout[0]);
                if (pad < 2) {
                    out.write(bout[1]);
                }
                if (pad < 1) {
                    out.write(bout[2]);
                }
                si = 0;
            }
        }
    }

    public void fromBase64(char[] in, int start, int length, StringBuilder out)
            throws IOException {
        int j, pad;
        byte b;
        byte[] bout;

        bout = new byte[3];

        j = 0;
        pad = 0;
        for (j = start; j < start + length; j++) {
            if (in[j] < 0 || in[j] > 255) {
                b = 64;
            } else {
                b = charMapDec[in[j]];
            }
            if (in[j] == 61) {
                pad++; // ASCII for '='
            }
            if (b == 64) {
                continue;
            }
            // System.err.print("'"+((char) in[j])+"' ("+in[j]+") "+b+" ("+j+") "+pad+"\n");
            sbin[si] = (byte) b;
            si++;
            if (si == 4) {
                bout[0] = (byte) (((sbin[0] & 0x3f) << 2) | ((sbin[1] & 0x30) >> 4));
                bout[1] = (byte) (((sbin[1] & 0x0f) << 4) | ((sbin[2] & 0x3c) >> 2));
                bout[2] = (byte) (((sbin[2] & 0x03) << 6) | (sbin[3] & 0x3f));
                out.append((char) bout[0]);
                if (pad < 2) {
                    out.append((char) bout[1]);
                }
                if (pad < 1) {
                    out.append((char) bout[2]);
                }
                si = 0;
            }
        }
    }

    public static void main(String args[]) {
        B64 b64;
        File fin, fin1, fin2, fout;
        FileInputStream fis, fis1, fis2;
        FileOutputStream fos;
        OutputStreamWriter osw;
        InputStreamReader isr;
        int i, c1, c2;
        String s;
        byte[] b1, b2, b3;
        ByteArrayOutputStream baos;

        System.err.println("Usage: B64 [-e] [-d] [<file>]");
        b64 = new B64();

        try {
            if (args.length == 0) {
                b1 = new byte[256];
                for (i = 0; i < 256; i++) {
                    b1[i] = (byte) i;
                }
                s = b64.toBase64(b1);
                System.err.println("Converted string: " + s);
                baos = new ByteArrayOutputStream();
                osw = new OutputStreamWriter(baos, "8859_1");
                osw.write(s);
                osw.close();
                b1 = b64.fromBase64(baos.toByteArray());
                for (i = 0; i < b1.length; i++) {
                    System.err.print(i + ":" + (0xFF & b1[i]) + " ");
                    if (i != (0xFF & b1[i])) {
                        System.err.println("PANIC! conversion failed");
                        break;
                    }
                }

                b2 = new byte[257];
                for (i = 0; i < 257; i++) {
                    b2[i] = (byte) i;
                }
                s = b64.toBase64(b2);
                System.err.println("Converted string: " + s);
                baos = new ByteArrayOutputStream();
                osw = new OutputStreamWriter(baos, "8859_1");
                osw.write(s);
                osw.close();
                b2 = b64.fromBase64(baos.toByteArray());
                for (i = 0; i < b2.length; i++) {
                    System.err.print(i + ":" + (0xFF & b2[i]) + " ");
                    if ((i & 0xFF) != (0xFF & b2[i])) {
                        System.err.println("PANIC! conversion failed");
                        break;
                    }
                }

                b3 = new byte[258];
                for (i = 0; i < 258; i++) {
                    b3[i] = (byte) i;
                }
                s = b64.toBase64(b3);
                System.err.println("Converted string: " + s);
                baos = new ByteArrayOutputStream();
                osw = new OutputStreamWriter(baos, "8859_1");
                osw.write(s);
                osw.close();
                b3 = b64.fromBase64(baos.toByteArray());
                for (i = 0; i < b3.length; i++) {
                    System.err.print(i + ":" + (0xFF & b3[i]) + " ");
                    if ((i & 0xFF) != (0xFF & b3[i])) {
                        System.err.println("PANIC! conversion failed");
                        break;
                    }
                }
            } else {
                // convert to base 64
                fin = new File(args[0]);
                fis = new FileInputStream(fin);
                i = args[0].lastIndexOf('.');
                if (i != -1) {
                    s = args[0].substring(0, i) + ".b64";
                } else {
                    s = args[0] + ".b64";
                }
                fout = new File(s);
                fos = new FileOutputStream(fout);
                osw = new OutputStreamWriter(fos, "8859_1");
                System.err.println("Encoding " + fin.getAbsolutePath() + " -> " + fout.getAbsolutePath());
                b64.toBase64(fis, osw);
                osw.close();
                fis.close();

                // convert from base 64
                fin = new File(s);
                fis = new FileInputStream(fin);
                isr = new InputStreamReader(fis, "8859_1");
                i = s.lastIndexOf('.');
                if (i != -1) {
                    s = s.substring(0, i) + ".tmp";
                } else {
                    s = s + ".tmp";
                }
                fout = new File(s);
                fos = new FileOutputStream(fout);
                System.err.println("Decoding " + fin.getAbsolutePath() + " -> " + fout.getAbsolutePath());
                b64.fromBase64(isr, fos);
                fos.close();
                fis.close();

                // compare original and decoded file
                fis1 = new FileInputStream(new File(args[0]));
                fis2 = new FileInputStream(new File(s));
                c1 = c2 = -1;
                for (;;) {
                    c1 = fis1.read();
                    c2 = fis2.read();
                    if (c1 == -1 || c2 == -1) {
                        break;
                    }
                    // System.err.print(c1+" "+c2+":");
                    if (c1 != c2) {
                        System.err.println("Failed! not equal!");
                        System.exit(-1);
                    }
                }
                if (c1 != -1) {
                    System.err.println("Failed! original file not finished!");
                    do {
                        System.err.print("- " + c1 + ":");
                    } while ((c1 = fis1.read()) != -1);
                }
                if (c2 != -1) {
                    System.err.println("Failed! decoded file not finished!");
                    do {
                        System.err.print(c2 + " -:");
                    } while ((c2 = fis2.read()) != -1);
                }
                if (c1 == -1 && c2 == -1) {
                    System.err.println("Success!");
                }
                fos.close();
                fis.close();
            }
        } catch (FileNotFoundException e) {
            System.err.println("File '" + args[0] + "' not found");
            System.exit(-1);
        } catch (IOException e) {
            System.exit(-1);
        }
    }
}
