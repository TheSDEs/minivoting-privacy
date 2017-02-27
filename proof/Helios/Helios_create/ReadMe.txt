
Installing java 
  - run the following sequence of commands:
    > sudo apt-get update
    > java -version
    > sudo apt-get install default-jre
    > sudo apt-get install default-jdk
  - more details here: https://www.digitalocean.com/community/tutorials/how-to-install-java-on-ubuntu-with-apt-get


Run this java class:
  - in folder Helios_create run the following:
    > javac Create.java
    > java  Create
  
  
Instruction for input:
  - First, you will be required to input your selection, one (or more) of the following:
    complete all, hom-std all, hom-weed all, mix-ord all, mix-perm all, 
                 hom-std one, hom-weed one, mix-ord one, mix-perm one.
  - Second, (available for a option that contains one): Introduce 5 values, each followed by Enter.
    The order of the operators is: Flabel, Publish, Policy, ValidInd and Relation
 
Check the easycrypt files
   - in folder public, run the command
   > make check
 
Details on type of input
  - on the all/one options:
    complete all, creates all versions of Helios-mix-ord, Helios-mix-perm, Helios-hom, Helios-hom-weed
	hom-std  all, creates all versions of Helios-hom
	hom-weed all, creates all versions of Helios-hom-weed
    mix-perm all, creates all versions of Helios-mix-perm (random order)
    mix-ord  all, creates one versions of Helios-mix-ord (lexicographic order)
    
	hom-std  one, creates one versions of Helios-hom
	hom-weed one, creates one versions of Helios-hom-weed
	mix-ord  one, creates one version  of Helios-mix-ord (lexicographic order)
	mix-perm one, creates one version  of Helios-mix-perm (random order)
	
  - on the one option (for invalid inputs value 0 is used). Additionally there exists the following
    constraint: for Publish empty, the Relation must return true
    Flabel options: type 0 for constant, 
	                     1 for empty, and 
						 2 for the identity function.
	Publish option: type 0 for empty, 
	                     1 for identity function, 
						 2 for last view,
						 3 for hash view, and 
						 4 for anon view.
	Policy option:  type 0 for last vote, 
	                     1 for first vote, and
						 2 for all votes.					 
	ValidInd option:type 0 for check proof, and 
		                 1 for return true.
	Relation option:type 0 for correct decryption, 
	                     1 for return true.
