library(shiny)
library(shinydashboard)
library(stockPortfolio)
library(PerformanceAnalytics)
library(highcharter)
library(DT)
library(dygraphs)
library(quadprog)

dlReturns <- function(ticker, freq=c('month', 'week', 'day'),
                  get=c('overlapOnly', 'all'),
                  start='1970-01-01', end=NULL){
  
  #______ Cleaning, Checking, and Initialization ______#
  
  startURL <- 'https://ichart.finance.yahoo.com/table.csv?s='
  URL      <- list()
  full     <- list()
  r        <- list()
  dates    <- list()
  ticker   <- as.character(ticker)
  n        <- length(ticker)
  start    <- as.Date(start)
  if(class(start) != "Date"){
    stop('Cannot read the start date.\n')
  }
  start    <- c(format(as.Date(start), "%m"),
                format(as.Date(start), "%d"),
                format(as.Date(start), "%Y"))
  start    <- as.numeric(start)
  if(is.null(end)[1]){
    end <- ''
  } else {
    end  <- as.Date(end)
    if(class(end) != "Date"){
      stop('Cannot read the end date.\n')
    }
    end <- c(format(as.Date(end), "%m"),
             format(as.Date(end), "%d"),
             format(as.Date(end), "%Y"))
    end <- as.numeric(end)
    end <- paste('&d=',end[1]-1, '&e=',end[2], '&f=',end[3], sep='')
  }
  
  #______ Data Retrieval ______#
  N       <- rep(-1, n)
  period  <- freq[1]
  freq    <- substr(freq[1],1,1)
  start   <- paste('&a=',start[1]-1, '&b=',start[2], '&c=',start[3], sep='')
  endURL  <- paste(start, end, "&g=", freq, "&ignore=.csv", sep="")
  minDate <- as.Date('2499-12-31')
  for(i in 1:n){
    URL        <- paste(startURL, ticker[i], endURL, sep='')
    d          <- read.delim(URL, TRUE, sep=',')
    full[[ticker[i]]]  <- d
    r[[i]]     <- (d[-dim(d)[1],7] - d[-1,7]) / d[-1,7]
    dates[[i]] <- as.Date(d[-dim(d)[1],1])
    minDate    <- min(c(minDate, d[,1]))
    N[i]       <- length(r[[i]])
  }
  uDates <- rev(sort(unique(c(dates, recursive=TRUE) - 1)))
  R      <- matrix(NA, length(uDates), n)
  rownames(R) <- as.character(as.Date(uDates, origin=minDate))
  for(i in 1:n){
    inR      <- match(as.character(dates[[i]]), rownames(R))
    R[inR,i] <- r[[i]]
  }
  if(get[1] == 'overlapOnly'){
    #===> this has been modified to work very well for months <===#
    toRemove <- which(apply(is.na(R), 1, any))
    if(all(diff(toRemove) == 1) | freq != 'm'){
      if(length(toRemove) > 0){
        R <- R[-toRemove, ]
      }
    } else {
      keep      <- rep(0, length(toRemove))
      theDates  <- as.Date(rownames(R)[toRemove], "%Y-%m-%d")
      theMonths <- months(theDates)
      theYears  <- format(theDates, '%Y')
      toCombine <- 0
      for(i in 1:(length(toRemove)-1)){
        cond1 <- theMonths[i] == theMonths[i+1]
        cond2 <- theYears[i] == theYears[i+1]
        cond3 <- abs(as.numeric(theDates[i] - theDates[i+1])) < 7 # extra precaution
        if((cond1 & cond2) | cond3){
          if(keep[i] > 0){ # if a 3rd or 4th date of the month is listed
            keep[i+1] <- keep[i]
          } else {
            toCombine <- toCombine+1
            keep[i]   <- toCombine
            keep[i+1] <- toCombine
          }
        }
      }
      # now we need to reorganize R
      if(any(keep == 0)){
        R <- R[-toRemove[keep == 0], ]
      }
      nRemoved <- 0
      for(i in 1:toCombine){
        combineThese <- toRemove[keep == i]
        inThisRow    <- combineThese[1]
        for(k in 2:length(combineThese)){
          thisRow <- combineThese[k]
          for(j in 1:ncol(R)){
            if(!is.na(R[thisRow-nRemoved,j])){
              R[inThisRow-nRemoved,j] <- R[thisRow-nRemoved,j]
            }
          }
          
        }
        R        <- R[-(combineThese[-1]-nRemoved),]
        nRemoved <- nRemoved + length(combineThese[-1])
      }
    }
  }
  if(!is.matrix(R)){
    R <- matrix(R, ncol=1)
    rownames(R) <- as.character(as.Date(uDates, origin=minDate))
  }
  colnames(R) <- ticker
  start <- rownames(R)[dim(R)[1]]
  end   <- rownames(R)[1]
  temp  <- list(R=R, ticker=ticker, period=period,
                start=start, end=end, full=full)
  class(temp) <- "stockReturns"
  return(temp)
}

eff.frontier <- function (returns, short="no", max.allocation=NULL,
                          risk.premium.up=.5, risk.increment=.005){
  # return argument should be a m x n matrix with one column per security
  # short argument is whether short-selling is allowed; default is no (short
  # selling prohibited)max.allocation is the maximum % allowed for any one
  # security (reduces concentration) risk.premium.up is the upper limit of the
  # risk premium modeled (see for loop below) and risk.increment is the
  # increment (by) value used in the for loop
  
  covariance <- cov(returns)
  n <- ncol(covariance)
  
  # Create initial Amat and bvec assuming only equality constraint
  # (short-selling is allowed, no allocation constraints)
  Amat <- matrix (1, nrow=n)
  bvec <- 1
  meq <- 1
  
  # Then modify the Amat and bvec if short-selling is prohibited
  if(short=="no"){
    Amat <- cbind(1, diag(n))
    bvec <- c(bvec, rep(0, n))
  }
  
  # And modify Amat and bvec if a max allocation (concentration) is specified
  if(!is.null(max.allocation)){
    if(max.allocation > 1 | max.allocation <0){
      stop("max.allocation must be greater than 0 and less than 1")
    }
    if(max.allocation * n < 1){
      stop("Need to set max.allocation higher; not enough assets to add to 1")
    }
    Amat <- cbind(Amat, -diag(n))
    bvec <- c(bvec, rep(-max.allocation, n))
  }
  
  # Calculate the number of loops
  loops <- risk.premium.up / risk.increment + 1
  loop <- 1
  
  # Initialize a matrix to contain allocation and statistics
  # This is not necessary, but speeds up processing and uses less memory
  eff <- matrix(nrow=loops, ncol=n+3)
  # Now I need to give the matrix column names
  colnames(eff) <- c(colnames(returns), "Std.Dev", "Exp.Return", "sharpe")
  
  # Loop through the quadratic program solver
  for (i in seq(from=0, to=risk.premium.up, by=risk.increment)){
    dvec <- colMeans(returns) * i # This moves the solution along the EF
    sol <- solve.QP(covariance, dvec=dvec, Amat=Amat, bvec=bvec, meq=meq)
    eff[loop,"Std.Dev"] <- sqrt(sum(sol$solution*colSums((covariance*sol$solution))))
    eff[loop,"Exp.Return"] <- as.numeric(sol$solution %*% colMeans(returns))
    eff[loop,"sharpe"] <- eff[loop,"Exp.Return"] / eff[loop,"Std.Dev"]
    eff[loop,1:n] <- sol$solution
    loop <- loop+1
  }
  
  return(as.data.frame(eff))
}


#### Load Data ####
load("data/etf_data.rda", envir = .GlobalEnv)

#### UI ####
ui <- dashboardPage(title = "Optimal ETF Portfolio",
                    dashboardHeader(title = "Optimal ETF Portfolio", titleWidth = 280),
                    dashboardSidebar(width = 280,
                                     tags$head(tags$script(src = "format_numbers.js")),
                                     sidebarMenu(
                                       menuItem(h4("Dashboard"), tabName = "dashboard"),
                                       selectizeInput("etfs", label = "Select ETFs",
                                                   choices = unique(etfList$CODE), multiple = TRUE,
                                                   options = list(maxItems = 8,
                                                                  placeholder = 'Select up to 8 ETFs')),
                                       dateRangeInput('dateRange',
                                                      label = "Select date range",
                                                      start = Sys.Date() - 1 - lubridate::years(3), 
                                                      end = Sys.Date() - 1,
                                                      format = "yyyy-mm-dd", weekstart = 1,
                                                      min = "2010-01-04", max = Sys.Date() - 1),
                                       selectizeInput("frequency", label = "Select frequency of returns",
                                                    choices = list("Daily" = "day",
                                                                   "Weekly" = "week",
                                                                   "Monthly" = "month"), selected = "week"),
                                       checkboxInput("shortSell", "Short-selling", FALSE),
                                       numericInput("portfolioValue", "Enter Portfolio Value ($)",
                                                    10000, min = 1000, max = 1000000),
                                       sliderInput("maxAllocation", "Maximum Allocation (%)",
                                                    35, min = 5, max = 95),
                                       tags$div(HTML("<center>"), actionButton("do", "Run Optimizer")),
                                       menuItem(h4("ETF List"), tabName = "etfList")
                                       )
                                     ),
                                     
                    dashboardBody(
                      tabItems(
                        tabItem(tabName = "dashboard",
                        fluidRow(
                          box(width = 6, status = "primary", title = "ETF Cumulative Returns", dygraphOutput("returnsPlot")),
                          box(width = 6, status = "primary", title = "Return and Volatility Plot", highchartOutput("portPlot"))
                          ),
                        fluidRow(
                          box(width = 6, status = "primary", title = "Optimal Portfolio Allocation", DT::dataTableOutput("table"), height = 420),
                          box(width = 6, status = "primary", title = "Optimal Portfolio Weights", highchartOutput("pie"), height = 420)
                          )
                      ),
                      tabItem("etfList", DT::dataTableOutput("etfTable"))
                      )
                    )
                  )

                    
#### SERVER ####
server <- function(input, output) {
  
  # reactive ETF returns table
  etfReturns <- eventReactive(input$do, {
    withProgress(message = "Downloading returns data...", value = 0, {
    returns <- dlReturns(ticker = sort(input$etfs), freq = input$frequency,
               start = input$dateRange[1], end = input$dateRange[2])
    return(returns$R)
    })
  })
  
  output$returnsPlot <- renderDygraph({
    dygraph(apply(etfReturns(), 2, function(z) {cumprod(1+z)-1})) %>%
      dyAxis("y", label = "%") %>%
      dyOptions(axisLineWidth = 1, fillGraph = FALSE, drawGrid = TRUE)
  })
  
  # run SIM where index is ASX200
  optim <- eventReactive(input$do, {
    withProgress(message = "Solving for optimal portfolio...", value = 0, {
      eff <- eff.frontier(returns=etfReturns(), short=ifelse(input$shortSell == TRUE,"yes","no"), max.allocation =  input$maxAllocation/100, risk.premium.up=.5, risk.increment=.001)
      eff.optim <- eff[eff$sharpe == max(eff$sharpe),][1,]
      
   # sim <- stockModel(etfReturns(), shortSelling = "no", model = "SIM", index = 1, freq = input$frequency)
  #  optSim <- optimalPort(sim)
    })
    return (eff.optim)
  })
  
  # Returns and risk plot
  output$portPlot <- renderHighchart({
   eff.optim <- optim()
   etfData <- t(cbind.data.frame(rbind(round(mean.geometric(etfReturns()), 4), 
                                       round(StdDev(etfReturns()), 4)),
                                 "Optimal Portfolio" = rbind(round(eff.optim$Exp.Return, 4), round(eff.optim$Std.Dev, 4))))
   etfData <- cbind.data.frame(Name = row.names(etfData), etfData * 100)
   names(etfData) <- c("Name","Expected Returns","StdDev")
    return(hchart(etfData, "scatter", hcaes(x = StdDev, y = `Expected Returns`, group = Name, size = 1)) %>%
             hc_add_theme(hc_theme_smpl()) %>%
             hc_yAxis(labels = list(format = "{value}%")) %>%
             hc_xAxis(labels = list(format = "{value}%")) %>%
             hc_tooltip(pointFormat = "Volatility: {point.x}% <br> Expected Return: {point.y}%")
    )
  })
  
  # Optimal portfolio weights pie chart
  output$pie <- renderHighchart({
    eff.optim <- optim()
    portfolioWeights <- data.frame(t(eff.optim[,-((length(eff.optim)-2):length(eff.optim))]))
    names(portfolioWeights) <- "wt"
    return(highchart() %>%
              hc_add_series_labels_values(row.names(portfolioWeights), (round(portfolioWeights$wt,4) * 100),
                                          type = "pie", size = 230,
                                          dataLabels = list(enabled = TRUE)) %>% 
              hc_legend(enabled = TRUE) %>% 
              hc_tooltip(valueDecimals = 2, pointFormat = "<b>{point.y}%</b>")
    )
  })
  
  # Optimal Portfolio Allocation table
  portfolioValue <- reactive({as.numeric(gsub(",", "", input$portfolioValue)) })
  
  output$table <- DT::renderDataTable({
    eff.optim <- optim()
    pWeights <- t(eff.optim[,-((length(eff.optim)-2):length(eff.optim))])[,1]
    portfolioAlloc <- cbind.data.frame(names(pWeights), 
                                       etfList[which(etfList$CODE %in% names(pWeights)), 2], 
                                       pWeights,
                                       round(pWeights * portfolioValue(),4))
    names(portfolioAlloc) <- c("ASX code", "ETF name", "Weight", "Value") 
    return(datatable(portfolioAlloc, rownames = FALSE, selection = "none", extensions = "Buttons",
                     options = list(dom = 'tB', buttons = c('copy', 'csv', 'excel'), scrollX = TRUE)) %>% 
                     formatCurrency("Value", '$') %>% 
                     formatPercentage("Weight", 1)
          )
  })
  
  output$etfTable <- DT::renderDataTable({
  	datatable(etfList, selection = "none", options = list(scrollX = TRUE, scrollY = TRUE, pageLength = 25), 
  						caption = 'List of major U.S. Exchange-Traded Funds (ETFs) traded in the USA.')
    })
  }

# Run the application 
shinyApp(ui = ui, server = server)