/********** NOCH NICHT FERTIG *************************/


/* Liest graphen im planarcode

 */
   
#include<stdio.h>
#include<memory.h>
#include<limits.h>


/*******************MAIN********************************/

main(argc,argv)

int argc;
char *argv[];


{
int zaehlen, welchergraph, knotenzaehler;
unsigned short code[6];
int lauf, nullenzaehler,i;
unsigned char ucharpuffer;

welchergraph=zaehlen=0;

if (argc==2) welchergraph=atoi(argv[1]);

for (;fread(&ucharpuffer,sizeof(unsigned char),1,stdin);)
  { if (ucharpuffer=='>') /* koennte ein header sein -- oder 'ne 62, also ausreichend fuer
			     unsigned char */
      { code[0]=ucharpuffer;
	lauf=1; nullenzaehler=0;
	code[1]=(unsigned short)getc(stdin);
	if(code[1]==0) nullenzaehler++; 
	code[2]=(unsigned short)getc(stdin);
	if(code[2]==0) nullenzaehler++; 
	lauf=3;
	/* jetzt wurden 3 Zeichen gelesen */
	if ((code[1]=='>') && ((code[2]=='p') ||(code[2]=='e')) ) /*garantiert header*/
	  { while ((ucharpuffer=getc(stdin)) != '<');
	    /* noch zweimal: */ ucharpuffer=getc(stdin); 
	    if (ucharpuffer!='<') { fprintf(stdout,"Problems with header -- single '<'\n"); exit(1); }
	    if (!fread(&ucharpuffer,sizeof(unsigned char),1,stdin)) exit(0);
	    /* kein graph drin */
	    lauf=1; nullenzaehler=0; }
	/* else kein header */
      }
    else { lauf=1; nullenzaehler=0; }

    zaehlen++; 

    if (ucharpuffer!=0) /* kann noch in unsigned char codiert werden ... */
                        { code[0]=ucharpuffer; 
			  fprintf(stdout,"\nGraph Nr. %d. Anzahl Knoten: %d\n",zaehlen,code[0]);
			  if (code[0]>0) fprintf(stdout,"1: ");
			  knotenzaehler=1;
			  for (i=1; i<lauf;i++)
			    { if (code[i]==0) { fprintf(stdout,"\n"); knotenzaehler++;
			                        if (knotenzaehler<=code[0]) 
                                                        fprintf(stdout,"%d: ",knotenzaehler); }
			    else fprintf(stdout," %d ",code[i]); }

			  while(nullenzaehler<code[0])
			    { code[lauf]=(unsigned short)getc(stdin);
			      if(code[lauf]==0) 
				{ nullenzaehler++;
				  fprintf(stdout,"\n"); 
			          if (nullenzaehler<code[0]) fprintf(stdout,"%d: ",nullenzaehler+1);
				}
			      else fprintf(stdout," %d ",code[lauf]);
			      }
			}
    else  { fread(code,sizeof(unsigned short),1,stdin);
            fprintf(stdout,"\nGraph Nr. %d. Anzahl Knoten: %d\n",zaehlen,code[0]);
	    if (code[0]>0) fprintf(stdout,"1: ");
	    nullenzaehler=0;
	    while(nullenzaehler<code[0])
	      { fread(code+1,sizeof(unsigned short),1,stdin);
		if(code[1]==0) { nullenzaehler++;
				  fprintf(stdout,"\n"); 
			          if (nullenzaehler<code[0]) fprintf(stdout,"%d: ",nullenzaehler+1);
				}
		else fprintf(stdout," %d ",code[1]);

	      }
           }


    /*    if (welchergraph == zaehlen) break;*/
  }

  

return(0);

}



