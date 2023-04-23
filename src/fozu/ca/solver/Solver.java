package fozu.ca.solver;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.NoSuchElementException;

/**
 * @author Kao, Chen-yi
 *
 */
public class Solver {

	private static final String TIMEOUT_ARG_PREFIX = "-T:";
	public static int TopDigitCarryInTimeout = 30;	// In seconds, TODO: default timeout threshold to Z3 default (none-set) ?
	
	// Z3 formulae to check
	private static String formulae = new String();
	private static String autoSmtFileName;



	/**<pre>
	 * Command line pattern:
	 * 	java fozu.caca.solver.Solver 
	 * 		or
	 * 	java -jar Solver.jar 
	 * 		then		
	 * [file] ( -qd(:)?(qn)?(,qn)* | -rd:(UB|In|LB) ) (-T:n)?
	 * </pre>
	 * @param args
	 */
	public static void main(String[] args) {
		try {
			// Reading template formula
			final String argSmtFileName = args[0];
			FileReader tr = new FileReader(argSmtFileName);
			for (char[] cbuf = new char[1]; tr.read(cbuf) != -1;)
				formulae += String.copyValueOf(cbuf);
			tr.close();
			formulae = formulae.replaceAll("\\(echo ", ";(echo ");	// Echo suppression replacement to make Z3 output without noise

			final String smtFileNameWOExt = argSmtFileName.substring(0, argSmtFileName.length()-4);	// extension '.' inclusive
			autoSmtFileName = smtFileNameWOExt + "auto.smt2";

			if (args.length > 2) TopDigitCarryInTimeout = Integer.parseUnsignedInt(args[2].split(":")[1]);
			
			final String argDegradeType = args[1];
			// TODO if (argDegradeType == null) throw InvalidCommandError; argDegradeType.regionMatches(...);
			
			String checkSat = null; 
			boolean needsMoreTimeout = false;
			if (argDegradeType.startsWith("-qd")) {
				final String[] argToken = argDegradeType.split(":", -1);	// "-qd:" default to ALL quantifiers existential
				final int argTokenSize = argToken.length;
				final QuantifierDegrader qd = new QuantifierDegrader(formulae);
				do {
					if (checkSat == null) System.out.println("* * * Timeout threshold: " + TopDigitCarryInTimeout + " sec. * * *");

					try {
						if (argTokenSize > 1) {
							final String[] forallQName = argToken[1].split(",");
							autoSmtFileName = smtFileNameWOExt + Arrays.toString(forallQName) + ".auto.smt2";
							checkSat = qd.nextCheck(forallQName);
						} else
							checkSat = qd.nextCheck();
					} catch (NoSuchElementException e) {
						System.out.println("No more degradings!");
						if (needsMoreTimeout) {
							checkSat = null;
							qd.resetCheck(); 
							TopDigitCarryInTimeout *= 2; 
							needsMoreTimeout = false; 
							continue;
						}
						else break;
					}
					
					// checking timeout/unknown
					if (checkSat.startsWith("timeout")) needsMoreTimeout = true;		// TODO: optional timeout upgrading
//					System.out.println("\\;\\;\\;\\;\\;" + tag);
//					// TODO: restoring the degrading tag comment or printing SAT/UNSAT result
//					// if (checkSat == "timeout" || checkSat == "unknown") restoreTemplate(tagIndex, tag);
//					//	else break; // and printing SAT/UNSAT information via the default standard output
					
					// printing SAT/UNSAT information via the default standard output
					int newLineIdx = checkSat.indexOf(System.getProperty("line.separator"));
					System.out.println(qd.getCurrentQuantifiers() + ":" + checkSat.substring(0, (newLineIdx == -1)?7:newLineIdx));
					
					// TODO: ;QuantDegrade1,2,...?
//					tag = ";QuantDegrade" + String.valueOf(i);	
//					tagIndex = formulae.indexOf(tag);
//					if (tagIndex == -1) break;
//					formulae = formulae.replaceFirst(tag, "");
//				} while (!checkSat.startsWith("!!!"));
				} while (argTokenSize == 1);
			}
			// TODO Quantifier degrading should be followed by the range one:
			//	parsing SAT model is necessary for automatically applying range degrading after the quantifier one
				
			switch (argDegradeType) {
			case "-rd:UB":
			case "-rd:In":
			case "-rd:LB":
				final CarryInRangeDegrader rd = new CarryInRangeDegrader(formulae, argDegradeType.substring(4));
				Thread tTDCI = new Thread(new Runnable() {
					public void run() {
						while (true) {
							try {
								Thread.sleep(TopDigitCarryInTimeout*60*1000);
							} catch (InterruptedException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
							rd.carryInTopDigit();
						}
					}
				});
				
				tTDCI.start();
				
				do {
					final String currentRange = rd.getCurrentRange();
					checkSat = rd.nextCheck();
					if (checkSat == null) break;

					// printing SAT/UNSAT information via the default standard output
					String satModels = rd.getSatRanges();
					String unsatRanges = rd.getUnsatRanges();
					String timeoutModels = rd.getTimeoutRanges();
					int crIndex = checkSat.indexOf("\r");
					System.out.println(currentRange + ":" + checkSat.substring(0, (crIndex == -1)?7:crIndex) + " => " +
							((satModels == null)?"":(satModels + ":sat;")) + 
							((unsatRanges == null)?"":(unsatRanges + ":unsat;")) + 
							((timeoutModels == null)?"":(timeoutModels + ":timeout;")));
					
					// alarming for any SAT result
//					if (checkSat.startsWith("sat")) while (true) {
//						Toolkit tk = Toolkit.getDefaultToolkit();
//						tk.beep(); 
//						try {tk.wait(500);} catch (InterruptedException e) {// doing nothing to keep beeping
//						}}
//				} while (!checkSat.startsWith("!!!"));
				} while (true);
				break;
			}

		} catch (FileNotFoundException e) {
			e.printStackTrace();
			System.exit(-1);
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		
		System.out.println("Done!");
		System.exit(0);
	}


	
	/**
	 * Calling Z3 with inherited environment setting.
	 * 
	 * @param formulae
	 * @return The (check-sat) result, including 'timeout', 'unknown', 'unsat' and 'sat' with model in the longest length
	 * @throws IOException
	 */
	static String z3check(String formulae) throws IOException {
		FileWriter tw = new FileWriter(autoSmtFileName);
		tw.write(formulae);
		tw.close();

		InputStream pipe = Runtime.getRuntime().
				exec(new String[] {"z3",TIMEOUT_ARG_PREFIX + TopDigitCarryInTimeout,"-smt2","--",autoSmtFileName}).getInputStream();
		// for debug use:
		//InputStream pipe = Runtime.getRuntime().
		//		exec(new String[] {"z3","-T:30","-smt2",autoSmtFileName}).getErrorStream();
		
		byte[] checkSatBuffer = new byte[1];
		String checkSat = new String();
		boolean nlAlready = false;
		do {	// treating \n\n as Z3 output termination signal
			try {
				pipe.read(checkSatBuffer);
				if (checkSatBuffer[0] == '\n') {if (nlAlready) break; else nlAlready = true;}	// TODO: System.getProperty("line.separator")
				else nlAlready = false;
			} catch (IOException e) {break;}
			checkSat += new String(checkSatBuffer);
		} while (true);
		pipe.close(); 
		return checkSat;
	}

}
