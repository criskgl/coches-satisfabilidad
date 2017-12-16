import java.io.*;
import java.util.Scanner;
import org.jacop.core.BooleanVar;
import org.jacop.core.Store;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

import java.util.ArrayList;


public class Coches {

	public static void main(String[] args) throws IOException {
		
		Store store = new Store();
		SatWrapper satWrapper = new SatWrapper(); 
		store.impose(satWrapper);					/* Importante: sat problem */
		
		String text = "";
		Scanner input = new Scanner(new File("parking.input"));
		
		System.out.println();	
		
		while(input.hasNext()) {
			 String i = input.next();
	         text += i;
		}
		
		int st = Character.getNumericValue(text.charAt(0)); //number of streets
		int pl = Character.getNumericValue(text.charAt(1)); //number of parking lots per street
		
		text = text.substring(2);
		
		System.out.println(text);

		//Matrices de VARIABLES
		BooleanVar isEmpty[][] = new BooleanVar[st][pl];
		BooleanVar catSup[][] = new BooleanVar[st][pl];
		BooleanVar catInf[][] = new BooleanVar[st][pl];
		BooleanVar catEq[][] = new BooleanVar[st][pl];
		BooleanVar bloqueaTiempo[][] = new BooleanVar[st][pl];
		BooleanVar mueveIzq[][] = new BooleanVar[st][pl];
		BooleanVar mueveDer[][] = new BooleanVar[st][pl];

		
		
		//Matrices de LITERALES
		int[][] isEmptyLiteral = new int[st][pl];
		int[][] catSupLiteral = new int[st][pl];
		int[][] catInfLiteral = new int[st][pl];
		int[][] catEqLiteral = new int[st][pl];
		int[][] bloqueaTiempoLiteral = new int[st][pl];
		int[][] mueveIzqLiteral = new int[st][pl];
		int[][] mueveDerLiteral = new int[st][pl];
 		
 		ArrayList<BooleanVar> variablesList=new ArrayList<BooleanVar>();			
 		BooleanVar[] allVariables = new BooleanVar[variablesList.size()];	
 		allVariables = variablesList.toArray(allVariables);
		
		for(int i = 0; i<st; i++) {
			for(int j = 0; j<pl; j++) {
				
				/* Creacion de variables booleanas*/
				isEmpty[i][j] = new BooleanVar(store, "La posicion "+j+" de la calle "+i+" esta: Vacia"); 
				catSup[i][j] = new BooleanVar(store, "La categoria de la posicion "+j+1+" de la calle "+i+" es SUPERIOR a la de la posicion "+j+" " +i); 
				catInf[i][j] = new BooleanVar(store, "La categoria de la posicion "+j+1+" de la calle "+i+" es INFERIOR a la de la posicion "+j+" " +i); 
				catEq[i][j] = new BooleanVar(store, "La categoria de la posicion "+j+1+" de la calle "+i+" es IGUAL a la de la posicion "+j+" " +i); 
				bloqueaTiempo[i][j] = new BooleanVar(store, "La posicion "+j+1+" de la calle "+i+" sale ANTES que la de la posicion "+j+" " +i); 
				mueveIzq[i][j] = new BooleanVar(store, "\t<\t");
				mueveDer[i][j] = new BooleanVar(store, "\t>\t"); 
				
				
 				variablesList.add(isEmpty[i][j]);
 				variablesList.add(catSup[i][j]);
 				variablesList.add(catInf[i][j]);
 				variablesList.add(catEq[i][j]);
 				variablesList.add(bloqueaTiempo[i][j]);
 				variablesList.add(mueveIzq[i][j]);
 				variablesList.add(mueveDer[i][j]);
 				
				
				/* Registramos las variables en el sat wrapper */
				satWrapper.register(isEmpty[i][j]);
				satWrapper.register(catSup[i][j]);
				satWrapper.register(catInf[i][j]);
				satWrapper.register(catEq[i][j]);
				satWrapper.register(bloqueaTiempo[i][j]);
				satWrapper.register(mueveIzq[i][j]);
				satWrapper.register(mueveDer[i][j]);

				isEmptyLiteral[i][j] = satWrapper.cpVarToBoolVar(isEmpty[i][j], 1, true);
				catSupLiteral[i][j] = satWrapper.cpVarToBoolVar(catSup[i][j], 1, true);
				catInfLiteral[i][j] = satWrapper.cpVarToBoolVar(catInf[i][j], 1, true);
				catEqLiteral[i][j] = satWrapper.cpVarToBoolVar(catEq[i][j], 1, true);
				bloqueaTiempoLiteral[i][j] = satWrapper.cpVarToBoolVar(bloqueaTiempo[i][j], 1, true);
				mueveIzqLiteral[i][j] = satWrapper.cpVarToBoolVar(mueveIzq[i][j], 1, true);
				mueveDerLiteral[i][j] = satWrapper.cpVarToBoolVar(mueveDer[i][j], 1, true);
				
			}
		}	
		
 		allVariables = variablesList.toArray(allVariables);

		/* Obtenemos los literales de todas las variables */
		int cont = 0;
 		
 		for(int i = 0; i<st; i++) {
 			for(int j = 0; j<pl; j++) {
 				if(text.charAt(cont) == '_')
 					addClause(satWrapper, isEmptyLiteral[i][j]);
 				else 
 					addClause(satWrapper, -isEmptyLiteral[i][j]);
 				cont+=2;
 			}
 		}
 		
 		
		cont = 0;
	
 		/*asignacion de valores a literales dependiendo del fichero de entrada*/
 		for(int i = 0; i<st; i++) {
 			for(int j = 0; j<pl; j++) {
 				if(j<pl-1) {
 					
 					if(j == 0) addClause(satWrapper, mueveIzqLiteral[i][j]);
 					
					if(text.charAt(cont) > text.charAt(cont + 2)){
						addClause(satWrapper, -catSupLiteral[i][j]);
						addClause(satWrapper, catInfLiteral[i][j]);
						addClause(satWrapper, -catEqLiteral[i][j]);
					}
					
					if(text.charAt(cont) < text.charAt(cont + 2)){
						addClause(satWrapper, catSupLiteral[i][j]);
						addClause(satWrapper, -catInfLiteral[i][j]);
						addClause(satWrapper, -catEqLiteral[i][j]);
					}
					
					if(text.charAt(cont) == text.charAt(cont + 2)){
						addClause(satWrapper, -catSupLiteral[i][j]);
						addClause(satWrapper, -catInfLiteral[i][j]);
						addClause(satWrapper, catEqLiteral[i][j]);
					}
					
					
 				}else if(j == pl-1){ //final de calle, todos los casos son falsos
 					
 					addClause(satWrapper, -catSupLiteral[i][j]);
 					addClause(satWrapper, -catInfLiteral[i][j]);
 					addClause(satWrapper, -catEqLiteral[i][j]);
 					addClause(satWrapper, mueveDerLiteral[i][j]);
 				}

 				cont+=2;
 			}
 		}
 		
 		cont = 1;/*Leemos desde el segundo valor de cada posicion*/
 		for(int i = 0; i<st; i++) {
 			for(int j = 0; j<pl; j++) {
 				if(j<pl-1) {
 					
					if(text.charAt(cont) > text.charAt(cont + 2)){
						addClause(satWrapper, -bloqueaTiempoLiteral[i][j]);
					}
						
					
					if(text.charAt(cont) < text.charAt(cont + 2)){
						addClause(satWrapper, bloqueaTiempoLiteral[i][j]);
					}

					if(text.charAt(cont) == text.charAt(cont + 2))
						addClause(satWrapper, -bloqueaTiempoLiteral[i][j]);
		
 				}else if(j == pl-1){ //final de calle		
 					addClause(satWrapper, -bloqueaTiempoLiteral[i][j]);	
 				}
 				cont+=2;
 			}
 		}
 		
 		//Clausulas
 		
 		for(int i = 0; i<st; i++) {
			for(int j = 1; j<pl-1; j++) {
			
	 		addClause(satWrapper, isEmptyLiteral[i][j-1], isEmptyLiteral[i][j], isEmptyLiteral[i][j+1], catSupLiteral[i][j-1], catInfLiteral[i][j], catEqLiteral[i][j], catEqLiteral[i][j-1]); // (x v y) 
	 		addClause(satWrapper, isEmptyLiteral[i][j-1], isEmptyLiteral[i][j], isEmptyLiteral[i][j+1], catSupLiteral[i][j-1], catInfLiteral[i][j], -bloqueaTiempoLiteral[i][j], catEqLiteral[i][j-1]); // (x v y) 
	 		addClause(satWrapper, isEmptyLiteral[i][j-1], isEmptyLiteral[i][j], isEmptyLiteral[i][j+1], catSupLiteral[i][j-1], catInfLiteral[i][j], catEqLiteral[i][j], bloqueaTiempoLiteral[i][j-1]); // (x v y) 
	 		addClause(satWrapper, isEmptyLiteral[i][j-1], isEmptyLiteral[i][j], isEmptyLiteral[i][j+1], catSupLiteral[i][j-1], catInfLiteral[i][j], -bloqueaTiempoLiteral[i][j], bloqueaTiempoLiteral[i][j-1]); // (x v y) 			
			
	 		addClause(satWrapper, mueveIzqLiteral[i][j], mueveDerLiteral[i][j]);
	 		
	 		addClause(satWrapper, mueveIzqLiteral[i][j], -isEmptyLiteral[i][j-1]);
	 		addClause(satWrapper, mueveIzqLiteral[i][j], -catSupLiteral[i][j-1]);
	 		addClause(satWrapper, mueveIzqLiteral[i][j], -catEqLiteral[i][j-1], -bloqueaTiempoLiteral[i][j-1]);
	 		
	 		addClause(satWrapper, mueveDerLiteral[i][j], -isEmptyLiteral[i][j+1]);
	 		addClause(satWrapper, mueveDerLiteral[i][j], -catInfLiteral[i][j]);
	 		addClause(satWrapper, mueveDerLiteral[i][j], -isEmptyLiteral[i][j], bloqueaTiempoLiteral[i][j]);

 			}
 		}		
 		
 				
	/* Resolvemos el problema */
 		
 		Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
		SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables, new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
		Boolean result = search.labeling(store, select);

		PrintWriter out = new PrintWriter(new FileWriter("parking.output"));
		
		if (result) {
			System.out.println("Satisfacible");
			
			for(int i = 0; i < st; i++){
				for(int j = 0; j < pl; j++){
					
					if(isEmpty[i][j].dom().value() == 1){
						out.write("\t_\t");
					}
					else if(mueveDer[i][j].dom().value() == 1){
						out.write(mueveDer[i][j].id());
					}
					
					else if(mueveIzq[i][j].dom().value() == 1){
						out.write(mueveIzq[i][j].id());
						
					}

					
				}out.write("\n");
			}
			
		} else{
			out.println("No Satisfacible");
		}
		out.close();
	}


	public static void addClause(SatWrapper satWrapper, int literal1){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		satWrapper.addModelClause(clause.toArray());
	}
	

	public static void addClause(SatWrapper satWrapper, int literal1, int literal2){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		satWrapper.addModelClause(clause.toArray());
	}


	public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		clause.add(literal3);
		satWrapper.addModelClause(clause.toArray());
	}
	
	
	public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3,int literal4, int literal5, int literal6, int literal7){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		clause.add(literal3);
		clause.add(literal4);
		clause.add(literal5);
		clause.add(literal6);
		clause.add(literal7);
		satWrapper.addModelClause(clause.toArray());
	}

}
