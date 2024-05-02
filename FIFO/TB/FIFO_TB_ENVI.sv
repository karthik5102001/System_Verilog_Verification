
///////////////////--INTERFACE--///////////////////////

interface fifo_if;               ///--INTERFACE--///
  logic clock,rd,wr;
  logic full,empty;
  logic [7:0] datain;
  logic [7:0] dataout;
  logic reset;
endinterface

///////////////////--TRANSACTION--////////////////////

class transaction;             ///--TRANSACTION--///
  rand bit control;
  bit [7:0] datain;
  bit [7:0] dataout;
  bit rd,wr,full,empty;
  bit reset;
  
  constraint A { control dist{1 := 50 , 0 := 50};}
endclass

////////////////////--GENERATOR--//////////////////////


class generator;            
  transaction tr,copy_tr; 
  mailbox #(transaction) gen_driv;
  int count = 0;
  int i = 0;
  
  event next,done;
  
  function new(mailbox #(transaction) gen_driv);
    this.gen_driv = gen_driv;
    tr= new();
  endfunction
  
  task run;
    begin
      repeat(count)
        begin
      assert(tr.randomize) else $display("RANDOMIZE FAILED");     //RANDOMIZE TRANSACTION
    i ++;
    copy_tr = new tr;                                             //COPY TRANSACTION
    gen_driv.put(copy_tr); 
          $display("+++++++++++++++++++++++++++++++++++++++++++++++++++++");
          $display("[GEN] controller Value sent to driver = %0d, iteration is %0d", tr.control,i);
          $display("+++++++++++++++++++++++++++++++++++++++++++++++++++++");
      @(next);                                                    ///--WAIT FOR NEXT--///
        end
    end
    -> done;                                                       ///--MARK THE DONE--///
  endtask
  
endclass


////////////////////////--DRIVER--///////////////////////////


class driver;
  transaction tr_drv,copy_tr_drv;
  mailbox #(transaction) gen_driv;
  virtual fifo_if fifo;
  
  function new(mailbox #(transaction) gen_driv);
    this.gen_driv = gen_driv;
    tr_drv = new();
  endfunction
  
  task reset;                                                    ///--RESET TASK--///
    @(posedge fifo.clock);
    fifo.reset <= 1'b1;
    fifo.rd <= 1'b0;
    fifo.wr <= 1'b0;
    fifo.datain <= 0;
    @(posedge fifo.clock);
    fifo.reset <= 1'b0;
    repeat(5) @(posedge fifo.clock);
    $display("---------------------------------");
    $display("[DRIVE] : RESET DONE");
    $display("---------------------------------");   
  endtask
  
  task write;
    @(posedge fifo.clock);
    fifo.reset <= 1'b0;
    fifo.rd <= 1'b0;
    fifo.wr <= 1'b1;
    fifo.datain <= $urandom_range(1,20);                   ///--RANDOM DATA--///
    @(posedge fifo.clock);
    fifo.wr <= 1'b0;
    $display("---------------------------");
    $display("[DRIVE] : DATA ARE : WR = %0d, RD = %0d, DATAIN = %0d, FULL = %0d , EMPTY = %0d",fifo.wr,fifo.rd,fifo.datain,fifo.full,fifo.empty);
    $display("[DRIVE] : WRITE DONE, DATAIN = %0d",fifo.datain);
    $display("---------------------------");  
    @(posedge fifo.clock);
  endtask
  
  task read;
    @(posedge fifo.clock);
    fifo.reset <= 1'b0;
    fifo.rd <= 1'b1;
    fifo.wr <= 1'b0;
    @(posedge fifo.clock);
    fifo.rd <= 1'b0;
    $display("---------------------------");
    $display("[DRIVE] : READ DONE ");
    $display("---------------------------");  
        @(posedge fifo.clock);
  endtask
 
     virtual task run();
     forever begin
       gen_driv.get( tr_drv );
       $display("[DRIV] : CONTROL = %0d",tr_drv.control);     
       if(tr_drv.control == 1)                                 ///--IF CONTROL IS 1 THEN WRITE--///
         begin $display("[DRIVE] : WRITE START");
         write();
         end
       else                                                   ///--IF CONTROL IS 0 THEN READ--///
         begin $display("[DRIVE] : READ START");
         read();
         end
     end
   endtask
  
endclass
             
             
////////////////////--MONITOR--///////////////////
             
class monitor ;
  transaction tr_mon,copy_trans;
  virtual fifo_if fifo;
  mailbox #(transaction) moni_scrb;
  
  function new(mailbox #(transaction) moni_scrb);
    this.moni_scrb = moni_scrb;
    tr_mon = new();
  endfunction
  

  task run();
    forever begin 
      repeat(2) @(posedge fifo.clock);
         tr_mon.wr = fifo.wr;                      ///--GET ALL THE DATA FROM FIFO AND ASSIGN TO LOCAL HANDEL--///
         tr_mon.rd = fifo.rd;
         tr_mon.datain =  fifo.datain;
         tr_mon.full = fifo.full;
         tr_mon.empty = fifo.empty;
      @(posedge fifo.clock);
         tr_mon.dataout = fifo.dataout;
          moni_scrb.put(tr_mon);
    $display("---------------------------");
    $display("[MONITOR] : FETCH DONE " );
    $display("[MONITOR] : DATA ARE : WR = %0d, RD = %0d, DATAIN = %0d, DATAOUT = %0d, FULL = %0d , EMPTY = %0d",tr_mon.wr,tr_mon.rd,tr_mon.datain,tr_mon.dataout,tr_mon.full,tr_mon.empty);
    $display("---------------------------");  
    end
  endtask

endclass
               
 
               
///////////////////--SCOREBOARD--//////////////////// 
               
 class scoreboard;
  
   mailbox #(transaction) moni_scrb ;  
  transaction tr_scrb , cov_data;          
  event next,done;
  bit [7:0] din[$];                          ///--DATA STORED IN FIFO--///
   bit [7:0] disp_INP[$];                    ///--DISPLAY DATA--///
   bit [7:0] disp_OUT[$];                    ///--DISPLAY DATA--///
   bit [7:0] temp;                           ///--TEMPORARY VARIABLE--///
  int err = 0, correct = 0, read = 0, write = 0, count = 0;   ///--VARIABLES FOR TRACKING TO DISPLAY--///
   
   
   covergroup coverage;                                     ///--COVERAGE--///
     option.comment = "RANDOM CONTROL SIGNAL";            
      option.per_instance = 1;                              
     CONTROL : coverpoint cov_data.control {
       bins JUST_HIT = {[1:0]};  }                        ///--JUST TO CHECK THE CONTROL--///
  endgroup
   
  
  function new(mailbox #(transaction) moni_scrb);
    this.moni_scrb = moni_scrb;  
    coverage = new();
  endfunction  

   
  task run();
    forever begin
      moni_scrb.get(tr_scrb);         
      cov_data = new tr_scrb;                              ////--COPY TRANSACTION--///
      coverage.sample();                                   ///--SAMPLE THE COVERAGE--///
      $display("[SCRB] : WR = %0d, RD = %0d, DATAIN = %0d DATAOUT = %0d FULL = %0d EMPTY = %0d", tr_scrb.wr, tr_scrb.rd, tr_scrb.datain, tr_scrb.dataout, tr_scrb.full, tr_scrb.empty);
      if(tr_scrb.wr == 1'b1) 
        begin
          if(tr_scrb.full == 1'b0)
            begin
              write = write + 1;
              din.push_front(tr_scrb.datain);                          ///--PUSH DATA IN FIFO--///
              $display("(LOCAL) PUSH FRONT SUCESSFULL");
              disp_INP.push_front(tr_scrb.datain);                     ///--PUSH SAME DATA TO DISPLAY--///
            //  $display("[SCRB] : DATA STORED 1  = %0d",tr_scrb.datain);
              $display("[SCRB] : WRITTEN VALUE FORM [MONI] = %0p",disp_INP);     ///--DISPLAY DATA--///
            end
          else
            $display("[SCRB] : FIFO_FULL");                                      ///--FIFO IS FULL--///
          $display("--------------------------");
        end
      
      if(tr_scrb.rd == 1'b1)
        begin
          if(tr_scrb.empty == 1'b0)
            begin
              read = read + 1;
              temp = din.pop_back();                                     ///--POP DATA FROM FIFO AND STORE IN TEMP--///
              $display("[SCRB] : (LOCAL) VALUE IN TEMP = %0d",temp);
              disp_OUT.push_front(tr_scrb.dataout);                       ///--PUSH DATAOUT's DATA INSIDE Q TO DISPLAY--///
              //$display("[SCRB] : DATA STORED 2  = %0d",tr_scrb.dataout);
              $display("[SCRB] : OUTPUT FROM [MONI] = %0p",disp_OUT);
              if(temp != tr_scrb.dataout)                                  ///--COMPARE DATAOUT's DATA WITH THE ONE STORED INSIDE TEMP--///
                begin 
                $display("[SCRB] : DATA MISMATCH");
                  err ++;
                end
              else 
                begin 
                  $display("[SCRB] : DATA MATCHED");
                  correct++;
                end
            end
         else
        $display("[SCRB] : MEMORY EMPTY");
        end
      $display("######################--END--########################");
           
      -> next;  	 	
    end
 endtask
   
      
    task result();
        $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
        $display("[SCRB] : COUNT = %0d",count); 
        $display("[SCRB] : WRITTEN COUNT ARE = %0d",write);
        $display("[SCRB] : READING COUNT ARE = %0d",read);
        $display("[SCRB] : DATA CORRECT ARE = %0d",correct);
        $display("[SCRB] : DATA INCORRECT ARE = %0d",err);
        $display("[SCRB] : DATAIN = %p",disp_INP);
        $display("[SCRB] : DATAOUT = %p",disp_OUT);
        $display("[SCRB] : COVERAGE PERCENT = %0f",coverage.get_coverage());
        $display("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");  
      endtask
  
endclass

      
///////////////////////--ENVIRONMENT--//////////////////////      
      
 class envinornment;
   transaction tr_env;
   generator gen;
   driver driv;
   monitor moni;
   scoreboard scrb;
   mailbox #(transaction) gen_driver;
   mailbox #(transaction) moni_scrb;
   virtual fifo_if fifo;  
   event done;
   
   
   function new (virtual fifo_if fifo);
     gen_driver = new;
     moni_scrb = new;
      gen = new(gen_driver);
     driv = new(gen_driver);
     moni = new(moni_scrb);
      scrb = new(moni_scrb);
     this.fifo = fifo;                     ///--INTERFACE--///
     driv.fifo = this.fifo;                ///--DRIVER INTERFACE--///
     moni.fifo = this.fifo;                ///--MONITOR INTERFACE--///
      scrb.next = gen.next;                
      done = gen.done;
   endfunction
   
   task run_1();
     fork
     gen.run();
     driv.run();
     moni.run();
     scrb.run();
       join_none
   endtask
   
   task display();                       ///--DISPLAY TASK--///
     wait(done.triggered);               ///--WAIT FOR DONE--///
     scrb.result();                     ///--DISPLAY THE RESULT--///
   endtask  
   
   task pre_test();
    driv.reset();                     ///--RESET--///
  endtask
   
   task run();
    // build();
     pre_test();
     run_1();
     display();
   endtask
   
 endclass
      
      
////////////////////--TOP-MODULE--//////////////////////////

module tb;
    
  fifo_if fif();
  
  FIFO dut (fif.clock, fif.reset, fif.wr, fif.rd, fif.datain, fif.dataout, fif.full, fif.empty);
  int count;
    
  initial begin
    fif.clock <= 0;
  end
    
  always #10 fif.clock <= ~fif.clock;
    
  envinornment env;
    
  initial begin
    env = new(fif);
    count = 10;
    env.gen.count = count;
    env.scrb.count = count;
    env.run();
    $finish;
  end
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
   
endmodule
      
      
      
