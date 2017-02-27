/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;

public class Create {


//----------------------------------------------------------------------------------
  //Flabel options: constant, empty, identity function
  static String flabel[] ={
	//constant:
	" type label.\n const lblx: label.\n op Flabel(id: ident) = lblx.\n",
	//empty:
        " type label = unit.\n const lblx: label.\n op Flabel(id: ident) = lblx.\n",
	//identity function:
         " type label = ident.\n const lblx: label.\n op Flabel(id: ident) = id.\n"};
//----------------------------------------------------------------------------------
  //Publish options: empty, identity function, last view, hash view, anon view
  static String publish[] ={
	//empty:
	" type pubBB = unit.\n const pubb: pubBB.\n op Publish(bb: (ident * label * (h_cipher * h_prf* h_data)) list) = pubb.\n",
	//identity function:
	" type pubBB = (ident * label * (h_cipher * h_prf* h_data)) list.\n op Publish(bb: (ident * label * (h_cipher * h_prf* h_data)) list)\n\t = bb. \n",
	//last view:
	" type pubBB = (ident * label * (h_cipher * h_prf* h_data)) list.\n op Publish(bb: (ident * label * (h_cipher * h_prf* h_data)) list)\n\t = keep_last bb.\n", 
	//hash view:
        " type pubBB = (ident * h_data) list.\n op extract_hash (b: (ident * label * (h_cipher * h_prf* h_data)))\n \t = (b.`1, b.`3.`3).\n op Publish (bb: (ident * label * (h_cipher * h_prf* h_data)) list)\n\t = map extract_hash (keep_last bb).",
	//anon view:
	" type pubBB = h_data list.\n op extract_anon (b: (ident * label * (h_cipher * h_prf* h_data)))\n\t = b.`3.`3.\n op Publish (bb: (ident * label * (h_cipher * h_prf* h_data)) list)\n\t = map extract_anon (keep_last bb). \n"};
//----------------------------------------------------------------------------------  
  // filter policy: last vote, first vote, keep all votes
  static String policy[] ={
	//last vote:
	" op Policy['a] (bb : (ident * 'a) list)\n\t = last_vote bb.\n",
	//first vote (or no-revote):
        " op Policy['a] (bb : (ident * 'a) list)\n\t = first_vote bb.\n", 
	//keep all votes:
	" op Policy['a] (bb : (ident * 'a) list)\n\t = all_votes bb.\n"};
  // Rho-lemmas proof: san_tallymap and san_mem
  static String hom_san_tally[] ={
	//proof for last vote policy:
	" rewrite /Policy.\n elim sbb =>//=.\n move => x l Hxl.\n pose f:= (fun (b : ident * h_cipher) =>\n\t (b.`1, (oget (decrypt sk b.`2)))).\n have ->:  (has (pred1 (f x).`1 \\o fst) (map f l)) = (has (pred1 x.`1 \\o fst) l).\n rewrite has_map.\n have ->: (preim f (pred1 (f x).`1 \\o fst)) = (pred1 x.`1 \\o fst).\n rewrite /preim.\n rewrite /(\\o) /pred1 //=.\n by smt.\n case (has (pred1 x.`1 \\o fst) l);\n  move: Hxl; rewrite -/f; smt.\n",
	//proof for first vote policy:
	" rewrite /Policy.\n elim sbb =>//=.\n smt.\n move => x l Hxl.\n rewrite /first_vote.\n pose f:= (fun (b : ident * h_cipher) =>\n\t (b.`1, (oget (decrypt sk b.`2)))).\n rewrite map_rev.\n have ->: last_vote (rev ((x.`1, oget (decrypt sk x.`2)) :: map f l)) =\n\t map f (last_vote (rev (x :: l))).\n have Hx: forall (y: (ident * h_cipher) list), \n\t last_vote (map f y) = map f (last_vote y).\n elim =>//=.\n move => y ll Hyl.\n have ->:  (has (pred1 (f y).`1 \\o fst) (map f ll)) = (has (pred1 y.`1 \\o fst) ll).\n\t by rewrite has_map.\n case (has (pred1 y.`1 \\o fst) ll);\n\t move: Hyl; rewrite -/f; smt.\n\t by smt.\n by done.\n",
	//proof for keep all votes policy:
	" rewrite /Policy.\n elim sbb =>//=.\n"};
  static String hom_san_mem[] ={
	//proof for last vote policy:
	" rewrite /Policy.\n elim sbb =>//=.\n move => x sbb.\n by smt.\n",
	//proof for first vote policy:
	" rewrite /Policy.\n elim sbb =>//=.\n smt.\n move => x sbb.\n rewrite /first_vote.\n have Hx: forall y, mem (last_vote y) b => mem y b.\n by elim =>//=; smt. \n by smt.\n",
	//proof for keep all votes policy:
	" rewrite /Policy.\n elim sbb =>//=.\n"};
//----------------------------------------------------------------------------------
  // validInd: check proof, do nothing
  static String validInd_op[] ={
	//check proof
	" op validInd = check_proof.\n",
	// do nothing
	" op validInd = check_nothing.\n"};
  static String validInd_mod[]={
	//check proof
	" module ValidInd = ValidProof.\n",
	//do nothing
	" module ValidInd = ValidNothing.\n"};
  // validInd lemmas proof: validInd_ax and C_ll 
  static String validInd_ax[] ={
	//proof for check proof
	" by proc; call (Verify_to_verify' gc (to_statement pk b.`2 b.`3.`1) b.`3.`2).\n",
	//proof for do nothing
	" by proc; auto.\n"};
  static String C_ll[] ={
	//proof for check proof
	" move => Ho; proc.\n by call (Cv_ll H Ho).\n",
	//proof for do nothing
	" move => Ho; proc.\n by auto.\n"};
//----------------------------------------------------------------------------------
  //relation: correct decryption, and return true
  static String relation[] ={
	//correct decryption:
	" module DecRel(Pe: PSpke.Prover, Ve: PSpke.Verifier,\n\t E: Scheme, H: HOracle.ARO) = DecRelation(E, H).\n",
	//return true:
	" module DecRel(Pe: PSpke.Prover, Ve: PSpke.Verifier,\n\t E: Scheme, H: HOracle.ARO) = NoRelation(E, H).\n"};
  //relation-lemmas proof: relCons and bound_vfr
  static String hom_relCons[] ={
	//proof for correct decryption:
	" proc; inline*; wp.\n while (HRO.RO.m = gh) (size wit.`2 -i); progress.\n\t wp; call Ve_ll.\n\t by auto; progress; smt.\n by auto; progress; smt.",
	//proof for return true:
	" by proc; auto."};
  static String mix_relCons[] ={
	//proof for correct decryption
	" proc; inline*; wp.\n while (HRO.RO.m = gh) (size wit.`2 -i); progress.\n\t wp; call Ve_ll.\n\t auto; progress.\n\t rewrite ltz_add2l //=.\n\t rewrite -(ltz_add2l (i{hr}+1)) //=.\n\t by rewrite addzAC //=.\n auto; progress.\n\t rewrite -lezNgt.\n by rewrite -(lez_add2r (-i0)).\n",
	//proof for return true
	" by proc; auto."};
  static String bound_vfr[] ={
	//proof for correct decryption:
	" Pr[VFR(IPKE(Pe, Ve),\n\t BVFR(MV(IPKE(Pe, Ve), Pz, Vz, ValidInd(Cv)), A),\n\t DecRelation(IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res].\n\t by byequiv =>//=; sim.\n by apply T1.\n",
	//proof for return true
	" Pr[VFR(IPKE(Pe, Ve),\n\t BVFR(MV(IPKE(Pe, Ve), Pz, Vz, ValidInd(Cv)), A),\n\t NoRelation(IPKE(Pe, Ve)), HRO.RO, Gx).main() @ &m : res].\n\t by byequiv =>//=; sim.\n by apply T2.\n"};
//----------------------------------------------------------------------------------


//create file name by adding stuff to helios_file
static String helios_name(int flabel_option, int publish_option, int policy_option, int validInd_option, int relation_option) {
  String helios_file="Fla_"+ flabel_option + "Pbb_"+ publish_option+ "Pol_"+ policy_option+ "Val_"+ validInd_option+ "Rel_"+ relation_option+ ".ec";
  return helios_file;
}

//create a easycrypt file based on input options, input file, and add it to outputFileile
static void helios_file(String outputFile, Boolean mix_or_hom, String inputFile, int flabel_option, int publish_option, int policy_option, int validInd_option, int relation_option) {
  try {
    File infile = new File(inputFile);
    File outfile= new File(outputFile);
    
    FileReader fileReader = new FileReader(infile);
    FileWriter fileWriter = new FileWriter(outfile);
    
    BufferedReader bufferedReader = new BufferedReader(fileReader);
    StringBuffer stringBuffer = new StringBuffer();
    
    String line="";
    while ((line = bufferedReader.readLine()) != null) {
        //1.flabel option
        if (line.contains("##1")){
            line = flabel[flabel_option];
	}
	//2.publish option
	if (line.contains("##2")) {
         line = publish[publish_option];
	}
	//3.policy option, and two lemmas
	if (line.contains("##3O")) {
         line = policy[policy_option];
	}
	if (line.contains("##3L1")) {
         line = hom_san_tally[policy_option];
	}
	if (line.contains("##3L2")) {
         line = hom_san_mem[policy_option];
	}
	//4.relation and two lemmas
	if (line.contains("##4M")) {
         line = relation[relation_option];
	}
	if (line.contains("##4L1")) {
	  // if hom option then
	  if(mix_or_hom){
            line = hom_relCons[relation_option];
	  }else{
	    //mix option
	    line = mix_relCons[relation_option];
	  }
	}
	if (line.contains("##4L2")) {
          line = bound_vfr[relation_option];
	}
	//5.validInd and two lemmas
	if (line.contains("##5O")) {
          line = validInd_op[validInd_option];
	}
	if (line.contains("##5M")) {
          line = validInd_mod[validInd_option];
	}
	if (line.contains("##5L1")) {
          line = validInd_ax[validInd_option];
	}
	if (line.contains("##5L2")) {
          line = C_ll[validInd_option];
	}
        fileWriter.write(line);
        fileWriter.write("\n");
        
    }
    fileReader.close();
    fileWriter.close();
    } catch (IOException e) {
        e.printStackTrace();
    }
}

//create all Helios files to putputFile, using inputFile and option mix_or_hom 
static void helios_not_weed(String outputFile, Boolean mix_or_hom, String inputFile) {
  int[] opt = new int[5];
  String ofile;
  //first all files with publish = not empty
  for(opt[0]=0; opt[0]<3; opt[0]++)
    for (opt[1]=1; opt[1]<5;opt[1]++)
	for (opt[2]=0; opt[2]<3;opt[2]++)
            for (opt[3]=0; opt[3]<2;opt[3]++)
		for (opt[4]=0; opt[4]<2;opt[4]++){ 
                    ofile = outputFile + helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
                    helios_file(ofile, mix_or_hom, inputFile, opt[0],opt[1],opt[2],opt[3],opt[4]);
		}	

  //lastly, all possible values with publish = empty
  opt[1] =0;//publish = empty
  opt[4] =1;//relation = return true
  for(opt[0]=0; opt[0]<3; opt[0]++)
    for (opt[2]=0; opt[2]<3;opt[2]++)
	for (opt[3]=0; opt[3]<2;opt[3]++){
            ofile = outputFile+ helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
            helios_file(ofile, mix_or_hom, inputFile,opt[0],opt[1],opt[2],opt[3],opt[4]);
	}	
}

//create all Helios files to putputFile, using inputFile and option mix_or_hom 
static void helios_weed(String outputFile, Boolean mix_or_hom, String inputFile) {
  int[] opt = new int[5];
  // injective label
  opt[0] = 2;
  String ofile;

  //first all files with publish = not empty
  for (opt[1]=1; opt[1]<5;opt[1]++)
    for (opt[2]=0; opt[2]<3;opt[2]++)
	for (opt[3]=0; opt[3]<2;opt[3]++)
            for (opt[4]=0; opt[4]<2;opt[4]++){ 
		ofile = outputFile + helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
		helios_file(ofile, mix_or_hom, inputFile, opt[0],opt[1],opt[2],opt[3],opt[4]);
            }	
  //lastly, all possible values with publish = empty
  opt[1] =0;//publish = empty
  opt[4] =1;//relation = return true
  for (opt[2]=0; opt[2]<3;opt[2]++)
    for (opt[3]=0; opt[3]<2;opt[3]++){
        ofile = outputFile + helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
	helios_file(ofile, mix_or_hom, inputFile,opt[0],opt[1],opt[2],opt[3],opt[4]);
    }	
}

static int[] keyboardOptions_Weed(BufferedReader bufferRead){
  int[] opt = new int[5];
  String option;  
  try{
    //Flabel option
    System.out.println("1. Based on weed, Flabel option is 2:");
    opt[0]=2; 
    
    //Publish option
    System.out.println("2. Publish option:");
    option = bufferRead.readLine();
    switch(option){
        case "0": opt[1]=0; break;
        case "1": opt[1]=1; break;
        case "2": opt[1]=2; break;
        case "3": opt[1]=3; break;
        case "4": opt[1]=4; break;
        default:  opt[1]=0; 
    }
    //Policy option
    System.out.println("3. Policy option:");
    option = bufferRead.readLine();
    switch(option){
        case "0": opt[2]=0; break;
        case "1": opt[2]=1; break;
        case "2": opt[2]=2; break;
        default:  opt[2]=0; 
    }
    //ValidInd option
    System.out.println("4. ValidInd option:");
    option = bufferRead.readLine();
    switch(option){
        case "0": opt[3]=0; break;
        case "1": opt[3]=1; break;
        default:  opt[3]=0; 
    }
    //Relation option
    System.out.println("5. Relation option:");
    if (opt[1]!=0){
        option = bufferRead.readLine();
        switch(option){
            case "0": opt[4]=0; break;
            case "1": opt[4]=1; break;
            default:  opt[4]=0; 
        }
    }else{
        System.out.println("Based on Publish empty, option 0 was selected for Relation ");
        opt[4]=0;
    }
    
  }catch(IOException e)
  {
    e.printStackTrace();
  }
  return opt;
}

static int[] keyboardOptions_noWeed(BufferedReader bufferRead){
  int[] opt = new int[5];
  String option;  
  try{
    //Flabel option
    System.out.println("1. Flabel option:");
    option = bufferRead.readLine();
    switch(option){
        case "0": opt[0]=0; break;
        case "1": opt[0]=1; break;
        case "2": opt[0]=2; break;
        default:  opt[0]=0; 
    }
    //Publish option
    System.out.println("2. Publish option:");
    option = bufferRead.readLine();
    switch(option){
        case "0": opt[1]=0; break;
        case "1": opt[1]=1; break;
        case "2": opt[1]=2; break;
        case "3": opt[1]=3; break;
        case "4": opt[1]=4; break;
        default:  opt[1]=0; 
    }
    //Policy option
    System.out.println("3. Policy option:");
    option = bufferRead.readLine();
    switch(option){
        case "0": opt[2]=0; break;
        case "1": opt[2]=1; break;
        case "2": opt[2]=2; break;
        default:  opt[2]=0; 
    }
    //ValidInd option
    System.out.println("4. ValidInd option:");
    option = bufferRead.readLine();
    switch(option){
        case "0": opt[3]=0; break;
        case "1": opt[3]=1; break;
        default:  opt[3]=0; 
    }
    //Relation option
    System.out.println("5. Relation option:");
    if (opt[1]!=0){
        option = bufferRead.readLine();
        switch(option){
            case "0": opt[4]=0; break;
            case "1": opt[4]=1; break;
            default:  opt[4]=0; 
        }
    }else{
        System.out.println("Based on Publish empty, option 0 was selected for Relation ");
        opt[4]=0;
    }
    
  }catch(IOException e)
  {
    e.printStackTrace();
  }
  return opt;
}
static void options() {
  //input file names
  String helios_hom_std  = "Test_hom_std/Helios_ver_";
  String helios_hom_weed = "Test_hom_weed/Helios_ver_";
  String helios_mix_ord  = "Test_mix_ord/Helios_ver_";
  String helios_mix_perm = "Test_mix_perm/Helios_ver_";

  String option="";
  String ofile="";
  System.out.println("Welcome to the Helios version(s) creation:");
  System.out.println("The following options are available: ");
  System.out.println("complete all, mix-ord all, mix-perm all, hom-std all, hom-weed all, and ");
  System.out.println("mix-ord one, mix-perm one, hom-std one, hom-weed one");
  System.out.println("(type help for more details, or check the ReadMe file)");
  try{
    BufferedReader bufferRead = new BufferedReader(new InputStreamReader(System.in));
    option = bufferRead.readLine();
    if (option.contains("help")){
	System.out.println("mix-ord  all, creates all versions of Helios-mix-ord (lexicographic order)");
	System.out.println("mix-perm all, creates all versions of Helios-mix-perm (random order)");
	System.out.println("hom-std  all, creates all versions of Helios-hom");
	System.out.println("hom-weed all, creates all versions of Helios-hom-weed");
	System.out.println("complete all,    creates all versions of Helios-mix-ord, Helios-mix-perm, Helios-hom, Helios-hom-weed");
	System.out.println("mix-ord  one, creates one version  of Helios-mix-ord (lexicographic order)");
	System.out.println("mix-perm one, creates one versions of Helios-mix-perm (random order)");
	System.out.println("hom-std  one, creates one versions of Helios-hom");
	System.out.println("hom-weed one, creates one versions of Helios-hom-weed");
	option = bufferRead.readLine();
    }
    // at least one all option
    if(option.contains("all")){
        // all all-options
        if (option.contains("complete all")){
            helios_not_weed(helios_hom_std,  true,  "Helios_hom_input.txt");
            helios_weed    (helios_hom_weed, true,  "Helios_hom_weed_input.txt");
            helios_not_weed(helios_mix_ord,  false, "Helios_mix_ord_input.txt");
            helios_not_weed(helios_mix_perm, false, "Helios_mix_perm_input.txt");
        }else{
        // one or more all options
            if (option.contains("hom-std all")){
                helios_not_weed(helios_hom_std,  true,  "Helios_hom_input.txt");
            }
            if (option.contains("hom-weed all")){
                helios_weed    (helios_hom_weed, true,  "Helios_hom_weed_input.txt");
            }
            if (option.contains("mix-ord all")){
                helios_not_weed(helios_mix_ord,  false, "Helios_mix_ord_input.txt");
            }
            if (option.contains("mix-perm all")){
                helios_not_weed(helios_mix_perm, false, "Helios_mix_perm_input.txt");
            }
        }
    }else{
        // maybe one or more one-options
        int[] opt;
        if (option.contains("one")){
            if (option.contains("hom-std one")){
                System.out.println("Option hom-std one detected:");
                System.out.println("Input");
                opt = keyboardOptions_noWeed(bufferRead);
                ofile = helios_hom_std + helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
                helios_file(ofile, true, "Helios_hom_input.txt", opt[0],opt[1],opt[2],opt[3],opt[4]);
                
            }
            if (option.contains("hom-weed one")){
                System.out.println("Option mix-ord one detected:");
                opt = keyboardOptions_Weed(bufferRead);
                ofile = helios_hom_weed + helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
                helios_file(ofile, true, "Helios_hom_weed_input.txt", opt[0],opt[1],opt[2],opt[3],opt[4]);
            }
            if (option.contains("mix-ord one")){
                System.out.println("Option mix-ord one detected:");
                opt = keyboardOptions_noWeed(bufferRead);
                ofile = helios_mix_ord + helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
                helios_file(ofile, false, "Helios_mix_ord_input.txt", opt[0],opt[1],opt[2],opt[3],opt[4]);
            }
            if (option.contains("mix-perm one")){
                System.out.println("Option mix-perm one detected:");
                opt = keyboardOptions_noWeed(bufferRead);
                ofile = helios_mix_perm + helios_name(opt[0],opt[1],opt[2],opt[3],opt[4]);
                helios_file(ofile, false, "Helios_mix_perm_input.txt", opt[0],opt[1],opt[2],opt[3],opt[4]);
            }
        }
  }
  }catch(IOException e)
  {
    e.printStackTrace();
  }
}

static void createFolders(){
  try{     
    new File("Test_hom_std").mkdirs();
    new File("Test_hom_weed").mkdirs();
    new File("Test_mix_ord").mkdirs();
    new File("Test_mix_perm").mkdirs();
  }catch(SecurityException se){
    //handle it
   } 

}
/**
* @param args the command line arguments
*/
public static void main(String[] args) {
  //create folders  
  createFolders();
  //options
  options();
}
    
}
