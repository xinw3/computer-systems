/*
 *                     proxy.c
 *
 * This is a proxy program that acts as an intermediary between clients 
 * and servers.
 * Clients make requests to access resources of servers.
 * 
 *                  Author: Xin Wang 
 *                  Andrew ID: xinw3
 * 
 */
#include <stdio.h>
#include "csapp.h"

/* Recommended max cache and object sizes */
#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400

/* You won't lose style points for including this long line in your code */
static const char *user_agent_hdr = "User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:10.0.3) Gecko/20120305 Firefox/10.0.3\r\n";
static const char *conn_hdr = "Connection: close\r\n";
static const char *proxy_conn_hdr = "Proxy-Connection: close\r\n";


void *thread(void *args);
void read_requesthdrs(rio_t *rp);
int parse_uri(char *uri, char *filename, char *cgiargs);
void parse_request(char *buf, char *host, char *port, char *pathname);
void forward_to_server(int connfd, char *pathname, char *host);

void serve_static(int fd, char *filename, int filesize);
void get_filetype(char *filename, char *filetype);
void serve_dynamic(int fd, char *filename, char *cgiargs);
void clienterror(int fd, char *cause, char *errnum, 
         char *shortmsg, char *longmsg);

/* $begin tinymain */
int main(int argc, char **argv) 
{
    int listenfd, *connfd;
    char hostname[MAXLINE], port[MAXLINE];
    socklen_t clientlen;
    struct sockaddr_storage clientaddr;
    pthread_t tid;
    /* Check command line args */
    if (argc != 2) {
    fprintf(stderr, "usage: %s <port>\n", argv[0]);
    exit(1);
    }

    listenfd = Open_listenfd(argv[1]);
    while (1) {
    clientlen = sizeof(clientaddr);
    //line:netp:tiny:accept
    connfd = Malloc(sizeof(connfd));
    connfd[0] = Accept(listenfd, (SA *)&clientaddr, &clientlen);
        Getnameinfo((SA *) &clientaddr, clientlen, hostname, MAXLINE, 
                    port, MAXLINE, 0);
        printf("Accepted connection from (%s, %s)\n", hostname, port);
    Pthread_create(&tid, NULL, thread, (void *)connfd);
    }
}
/* $end tinymain */

/*
 * thread - handle one HTTP request/response transaction
 */
/* $begin thread */
void *thread(void *args) 
{
    Pthread_detach(pthread_self());
    int fd = *(int *)args;
    char buf[MAXLINE], method[MAXLINE], uri[MAXLINE], version[MAXLINE];
    rio_t rio;
    char pathname[MAXLINE], port[MAXLINE], host[MAXLINE];
    int clientfd;

    /* Read request line and headers */
    Rio_readinitb(&rio, fd);
    if (!Rio_readlineb(&rio, buf, MAXLINE))
        return NULL;
    // Parse request
    sscanf(buf, "%s %s %s", method, uri, version);
    // Begin request error
    if (strcasecmp(method, "GET")) {
        clienterror(fd, method, "501", "Not Implemented",
                    "Proxy does not implement this method");
        return NULL;
    }
 
    // Parse request.
    sprintf(port, "80");
    parse_request(buf, host, port, pathname);
    // Send request to server.
    clientfd = Open_clientfd(host, port);
    forward_to_server(clientfd, pathname, host);
    // Read response.
    Rio_readinitb(&rio, clientfd);
    int size = 0;
    while ((size = Rio_readlineb(&rio, buf, MAXLINE)) > 0)
    {
        Rio_writen(fd, buf, size);
        printf("%s\n", buf);
    }
    Free(args);
    Close(fd);
    Close(clientfd);
    return NULL;
}
/* $end thread */

void parse_request(char *buf, char *host, char *port, char *pathname)
{
    char *temp, *first, *next, *p;
    printf("%s\n", buf);
    // Get host name.
    if ((temp = strstr(buf, "http://")) == NULL)
    {
        return;
    }
    // Point to the host name.
    first = temp + 7;
    // Point to "/" after host name to get path name.
    if ((temp = strstr(first, "/")) != NULL)
    {
        next = temp;
    }
    // Point to the space after path name.
    if ((temp = strstr(next, " ")) != NULL)
    {
        p = temp;
    }
    // Get pathname.
    strncpy(pathname, next, p - next);
    pathname[p - next] = '\0';
    // Point to the ":" after host name if any.
    if (((temp = strstr(first, ":")) != NULL) && (temp < next))  
    {
        // Get port.
        strncpy(port, temp + 1, next - temp - 1);
        port[next - temp - 1] = '\0';
        next = temp;
    }
    // Get host name.
    strncpy(host, first, next - first);
    host[next - first] = '\0';
    printf("%s\n", port);
    printf("%s\n", host);
    printf("%s\n", pathname);
}

void forward_to_server(int connfd, char *pathname, char *host)
{
    char req[MAXLINE];
    // Forward request.
    sprintf(req, "GET %s HTTP/1.0\r\n", pathname);
    Rio_writen(connfd, req, strlen(req));
    printf("%s\n", req);
    // Forward hostname.
    sprintf(req, "HOST: %s\r\n", host);
    Rio_writen(connfd, req, strlen(req));
    printf("%s\n", req);
    // Forward User-Agent.
    sprintf(req, user_agent_hdr);
    Rio_writen(connfd, req, strlen(req));
    printf("%s\n", req);
    // Forward Connection.
    sprintf(req, conn_hdr);
    Rio_writen(connfd, req, strlen(req));
    printf("%s\n", req);
    // Forward Proxy-Connection.
    sprintf(req, proxy_conn_hdr);
    Rio_writen(connfd, req, strlen(req));
    printf("%s\n", req);
    // End.
    Rio_writen(connfd, "\r\n", 2);
}


/*
 * clienterror - returns an error message to the client
 */
/* $begin clienterror */
void clienterror(int fd, char *cause, char *errnum, 
         char *shortmsg, char *longmsg) 
{
    char buf[MAXLINE], body[MAXBUF];

    /* Build the HTTP response body */
    sprintf(body, "<html><title>Proxy Error</title>");
    sprintf(body, "%s<body bgcolor=""ffffff"">\r\n", body);
    sprintf(body, "%s%s: %s\r\n", body, errnum, shortmsg);
    sprintf(body, "%s<p>%s: %s\r\n", body, longmsg, cause);
    sprintf(body, "%s<hr><em>The Proxy server</em>\r\n", body);

    /* Print the HTTP response */
    sprintf(buf, "HTTP/1.0 %s %s\r\n", errnum, shortmsg);
    Rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-type: text/html\r\n");
    Rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-length: %d\r\n\r\n", (int)strlen(body));
    Rio_writen(fd, buf, strlen(buf));
    Rio_writen(fd, body, strlen(body));
}
/* $end clienterror */
